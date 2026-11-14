/*
 * The exclusive UDP bind of net/streams: bind a socket that the Lean
 * runtime's libuv binding holds, with no address reuse.
 *
 * Lean v4.34 binds every UDP socket with `UV_UDP_REUSEADDR`
 * (src/runtime/uv/udp.cpp, line 106), and `Std.Async.UDP` has no bind
 * without it. On Linux, SO_REUSEADDR lets a port-0 bind take a port that
 * another socket already holds. The kernel then gives each datagram to
 * one of the two. One node receives another node's packets, and a
 * socket's wake datagram can reach the wrong socket. So the shim opens
 * and binds the socket itself, with no reuse option. Then it hands the
 * descriptor to the libuv handle inside Lean's socket object. Both UDP
 * users call it: `Streams.Udp` (discv5) and `net/quic`'s endpoint.
 *
 * The shim depends on three facts of the toolchain. A toolchain bump
 * checks each one again before it removes the guard below:
 * - The first field of `lean_uv_udp_socket_object` is the `uv_udp_t`
 *   pointer (src/runtime/uv/udp.h, line 26).
 * - `lean_uv_udp_new` makes the handle with `uv_udp_init`, which opens
 *   no descriptor (src/runtime/uv/udp.cpp, line 79). So `uv_udp_open`
 *   takes ours.
 * - libuv's `uv_udp_open` sets the reuse option on the descriptor it
 *   takes (libuv v1.48.0, src/unix/udp.c, line 1040, `uv__set_reuse`).
 *   So the shim clears that option again after the call.
 */
#include <lean/lean.h>
#include <errno.h>
#include <fcntl.h>
#include <netinet/in.h>
#include <string.h>
#include <sys/socket.h>
#include <unistd.h>

#if !(LEAN_VERSION_MAJOR == 4 && LEAN_VERSION_MINOR == 34)
#error "udpbind.c: re-check the exclusive bind against src/runtime/uv/udp.h, src/runtime/uv/udp.cpp, and the toolchain's libuv uv_udp_open (packages/net/streams/docs/ARCHITECTURE.md, the exclusive bind)"
#endif

/* libuv ships in the toolchain's libuv.a with no header. The handle is
 * an opaque pointer, and `uv_os_sock_t` is int on Unix. */
extern int uv_udp_open(void *handle, int sock);

static lean_obj_res errno_error(int e) {
    return lean_io_result_mk_error(lean_decode_io_error(e, NULL));
}

/* An address crosses as bytes: the family (4 or 6), the address in
 * network order (4 or 16 bytes), then the port, big-endian. */
static int addr_from_bytes(b_lean_obj_arg b, struct sockaddr_storage *ss, socklen_t *len) {
    const uint8_t *p = lean_sarray_cptr(b);
    size_t n = lean_sarray_size(b);
    memset(ss, 0, sizeof *ss);
    if (n == 7 && p[0] == 4) {
        struct sockaddr_in *a = (struct sockaddr_in *)ss;
        a->sin_family = AF_INET;
        memcpy(&a->sin_addr, p + 1, 4);
        a->sin_port = htons((uint16_t)(p[5] << 8 | p[6]));
        *len = sizeof *a;
        return 1;
    }
    if (n == 19 && p[0] == 6) {
        struct sockaddr_in6 *a = (struct sockaddr_in6 *)ss;
        a->sin6_family = AF_INET6;
        memcpy(&a->sin6_addr, p + 1, 16);
        a->sin6_port = htons((uint16_t)(p[17] << 8 | p[18]));
        *len = sizeof *a;
        return 1;
    }
    return 0;
}

/* Bind the Lean socket `sock` (`Std.Internal.UV.UDP.Socket`) to the
 * address bytes `addr`, with no address reuse. The caller calls it once,
 * on a socket fresh from `Std.Async.UDP.Socket.mk`, before any receive
 * or send. libuv's loop thread does not touch the handle before then, so
 * the call needs no loop lock. A bind to a port that another socket
 * holds fails with EADDRINUSE. */
LEAN_EXPORT lean_obj_res leanp2p_udp_bind(b_lean_obj_arg sock, b_lean_obj_arg addr) {
    struct sockaddr_storage ss;
    socklen_t len;
    if (!addr_from_bytes(addr, &ss, &len)) return errno_error(EINVAL);
    int fd = socket(ss.ss_family, SOCK_DGRAM, 0);
    if (fd < 0) return errno_error(errno);
    if (fcntl(fd, F_SETFD, FD_CLOEXEC) != 0 || bind(fd, (struct sockaddr *)&ss, len) != 0) {
        int e = errno;
        close(fd);
        return errno_error(e);
    }
    void **object = (void **)lean_get_external_data(sock);
    int rv = uv_udp_open(object[0], fd);
    if (rv != 0) {
        /* libuv's error codes on Unix are the negated errno values. */
        close(fd);
        return errno_error(-rv);
    }
    /* The handle owns the descriptor now, and the runtime's finalizer
     * closes it. libuv set the reuse option. Clear it, so no later bind
     * can share the port. */
    int off = 0;
    if (setsockopt(fd, SOL_SOCKET, SO_REUSEADDR, &off, sizeof off) != 0) return errno_error(errno);
#ifdef SO_REUSEPORT
    if (setsockopt(fd, SOL_SOCKET, SO_REUSEPORT, &off, sizeof off) != 0) return errno_error(errno);
#endif
    return lean_io_result_mk_ok(lean_box(0));
}

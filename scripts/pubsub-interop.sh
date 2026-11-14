#!/usr/bin/env bash
# Pubsub interoperability with go-libp2p-pubsub v0.19.0 over go-libp2p
# v0.51.0: signed peer records, floodsub, and gossipsub peer exchange.
#
# The go side (scripts/pubsub-go) builds from the clones beside the repo
# (../p2p/go-libp2p and ../p2p/go-libp2p-pubsub, which its go.mod
# replaces the modules with), with the host Go toolchain on two cores.
# The Lean side is the `pubsub-interop` executable (Tests/Interop/Pubsub).
#
# 1. record: go consumes our signed peer record, and we open go's (the
#    byte vector of Tests/Record.lean is go's; this rerun checks the
#    other direction).
# 2. floodsub: a go floodsub-only node and our node with floodsub on
#    exchange one message each way.
# 3. px-accept: go node G runs gossipsub with peer exchange and a mesh
#    bound of two, and H1 and H2 fill its mesh. We join; G prunes our
#    GRAFT with H1 and H2 and their records. We pass when we connect to
#    one of them.
# 4. px-send: we run with peer exchange and a mesh bound of two; go nodes
#    A1 and A2 fill our mesh, then A3 joins. Our prune of A3 names A1 and
#    A2 with their records, and A3 passes when it connects to one of them.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
out="$root/.tmp/pubsub-interop"
tool="$out/pubsub-go"
lean="$root/.lake/build/bin/pubsub-interop"
libp2p_rev=03349944847387886bf06b65993b2a03c1e6d12d
pubsub_rev=c2780c046ac2f96ce5be7959160df3160df70a59
pids=()

cleanup() {
  for p in "${pids[@]}"; do
    if kill -0 "$p" 2>/dev/null; then
      kill "$p"
      wait "$p" || true
    fi
  done
  pids=()
}
trap cleanup EXIT

check_rev() {
  local have
  have=$(git -C "$1" rev-parse HEAD)
  if [[ "$have" != "$2" ]]; then
    echo "pubsub-interop: $1 is at $have, want $2" >&2
    exit 2
  fi
}

mkdir -p "$out"
check_rev "$root/../p2p/go-libp2p" "$libp2p_rev"
check_rev "$root/../p2p/go-libp2p-pubsub" "$pubsub_rev"
if [[ ! -x "$tool" ]]; then
  (cd "$root/scripts/pubsub-go" && GOFLAGS=-p=2 GOMAXPROCS=2 nice -n19 go build -o "$tool" .)
fi
[[ -x "$lean" ]] || { echo "pubsub-interop: build pubsub-interop first" >&2; exit 2; }

# Start a go node in the background with its output in $out/$1.out, and
# wait for its ADDR line; sets `addr` and `pid`. It runs in this shell,
# not in a command substitution, so `pids` keeps the process for the
# cleanup.
go_node() {
  local name=$1
  shift
  "$tool" node "$@" >"$out/$name.out" 2>"$out/$name.err" &
  pid=$!
  pids+=("$pid")
  addr=
  for _ in $(seq 1 100); do
    addr=$(sed -n 's/^ADDR //p' "$out/$name.out")
    [[ -n "$addr" ]] && return 0
    sleep 0.1
  done
  echo "pubsub-interop: no address from $name" >&2
  exit 1
}

# The peer id at the end of a full multiaddr.
peer_of() { echo "${1##*/p2p/}"; }

status=0
pass() { echo "$1: PASS"; }
failed() { echo "$1: FAIL"; status=1; }

# 1. Records.
if "$tool" verify "$("$lean" record 9 /ip4/127.0.0.1/tcp/4002)" >"$out/verify.out"; then
  cat "$out/verify.out"
  pass "record lean-to-go"
else
  failed "record lean-to-go"
fi

# 2. Floodsub, both directions in one run: we wait for go's message, and
# the go node exits 0 once ours arrives.
go_node flood -seed F -router floodsub -publish from-go -expect from-lean -timeout 30
if "$lean" floodsub "$addr" >"$out/lean-flood.out" 2>"$out/lean-flood.err" && wait "$pid"; then
  grep -h -m1 '^GOT from-lean' "$out/flood.out"
  grep -h '^LEAN-GOT' "$out/lean-flood.out"
  pass "floodsub"
else
  cat "$out/lean-flood.out" "$out/lean-flood.err" "$out/flood.out" "$out/flood.err"
  failed "floodsub"
fi
cleanup

# 3. px-accept: G with H1 and H2 in a full mesh.
go_node pxg -seed G -px -d 2 -dlo 1 -dhi 2 -timeout 40
g=$addr
go_node pxh1 -seed H -connect "$g" -timeout 40
go_node pxh2 -seed I -connect "$g" -timeout 40
# Let G's mesh fill before we graft.
sleep 3
if "$lean" px-accept "$g" >"$out/lean-pxa.out" 2>"$out/lean-pxa.err"; then
  cat "$out/lean-pxa.out"
  pass "px go-to-lean"
else
  cat "$out/lean-pxa.out" "$out/lean-pxa.err"
  failed "px go-to-lean"
fi
cleanup

# 4. px-send: our node with A1 and A2 in a full mesh, then A3.
port=${PUBSUB_LEAN_PORT:-30455}
"$lean" px-send "$port" 25 >"$out/lean-pxs.out" 2>"$out/lean-pxs.err" &
pids+=($!)
l=
for _ in $(seq 1 100); do
  l=$(sed -n 's/^ADDR //p' "$out/lean-pxs.out")
  [[ -n "$l" ]] && break
  sleep 0.1
done
[[ -n "$l" ]] || { echo "pubsub-interop: no address from the Lean node" >&2; exit 1; }
go_node pxa1 -seed A -connect "$l" -timeout 30
a1=$addr
go_node pxa2 -seed B -connect "$l" -timeout 30
a2=$addr
sleep 3
if "$tool" node -seed C -connect "$l" -watch "$(peer_of "$a1")" -watch "$(peer_of "$a2")" \
    -timeout 15 >"$out/pxa3.out" 2>"$out/pxa3.err"; then
  grep -E '^(CONNECTED|DONE)' "$out/pxa3.out"
  pass "px lean-to-go"
else
  cat "$out/pxa3.out" "$out/pxa3.err" "$out/lean-pxs.out" "$out/lean-pxs.err"
  failed "px lean-to-go"
fi

exit "$status"

#!/usr/bin/env bash
# Partial-messages interoperability (gossipsub v1.3) with rust-libp2p's
# gossipsub, the implementation Lighthouse runs, built from the clone
# beside the repo (../p2p/rust-libp2p at c449090) with its
# `partial-messages` feature.
#
# The helper (scripts/pubsub-rust) dials our `pubsub-interop
# partial-listen` node, which requests partial messages on the topic.
#
# 1. rust requester: each side gets the other's partial data, and neither
#    gets a full message from the other.
# 2. rust supporter: rust gets our metadata without the data, and we get
#    its data.
#
# The helper builds with cargo on two cores into
# .tmp/pubsub-interop/rust-target.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
out="$root/.tmp/pubsub-interop"
lean="$root/.lake/build/bin/pubsub-interop"
helper="$out/rust-target/release/pubsub-rust"
rust_rev=c449090f49b5ae2338e8f0727be98e0a739ba135
port=${PUBSUB_LEAN_PORT:-30456}
pid=

cleanup() {
  if [[ -n "$pid" ]] && kill -0 "$pid" 2>/dev/null; then
    kill "$pid"
    wait "$pid" || true
  fi
  pid=
}
trap cleanup EXIT

have=$(git -C "$root/../p2p/rust-libp2p" rev-parse HEAD)
if [[ "$have" != "$rust_rev" ]]; then
  echo "pubsub-rust-interop: ../p2p/rust-libp2p is at $have, want $rust_rev" >&2
  exit 2
fi
mkdir -p "$out"
if [[ ! -x "$helper" ]]; then
  CARGO_BUILD_JOBS=2 nice -n19 cargo build --release \
    --manifest-path "$root/scripts/pubsub-rust/Cargo.toml" --target-dir "$out/rust-target"
fi
[[ -x "$lean" ]] || { echo "pubsub-rust-interop: build pubsub-interop first" >&2; exit 2; }

status=0

# Start our node in the background and wait for its ADDR line; sets `addr`.
lean_node() {
  "$lean" partial-listen "$port" >"$out/lean-$1.out" 2>"$out/lean-$1.err" &
  pid=$!
  addr=
  for _ in $(seq 1 100); do
    addr=$(sed -n 's/^ADDR //p' "$out/lean-$1.out")
    [[ -n "$addr" ]] && return 0
    sleep 0.1
  done
  echo "pubsub-rust-interop: no address from the Lean node" >&2
  exit 1
}

# 1. rust requests partial messages.
lean_node rustr
if "$helper" request "$addr" 30 >"$out/rustr.out" 2>"$out/rustr.err" && wait "$pid" &&
    ! grep -q '^GOT from-lean-full' "$out/rustr.out"; then
  pid=
  grep -h -m1 '^PARTIAL .* data=from-lean-partial' "$out/rustr.out"
  cat "$out/lean-rustr.out"
  echo "partial rust requester: PASS"
else
  cat "$out/rustr.out" "$out/rustr.err" "$out/lean-rustr.out" "$out/lean-rustr.err"
  echo "partial rust requester: FAIL"
  status=1
fi
cleanup

# 2. rust only supports partial messages.
lean_node rusts
if "$helper" support "$addr" 30 >"$out/rusts.out" 2>"$out/rusts.err" && wait "$pid" &&
    ! grep -q '^PARTIAL .* data=from-lean' "$out/rusts.out"; then
  pid=
  grep -h -m1 '^PARTIAL .* meta=meta-lean' "$out/rusts.out"
  cat "$out/lean-rusts.out"
  echo "partial rust supporter: PASS"
else
  cat "$out/rusts.out" "$out/rusts.err" "$out/lean-rusts.out" "$out/lean-rusts.err"
  echo "partial rust supporter: FAIL"
  status=1
fi

exit "$status"

#!/usr/bin/env bash
# discv5 interoperability with Lighthouse's implementation: the sigp
# discv5 crate at 0.12.0 (lighthouse Cargo.lock), both directions.
#
# rust-to-lean: the suite binary serves in `discv5serve` mode and prints
# its ENR; the helper (scripts/discv5-rust) PINGs it, FINDNODEs it at
# distance 0, and TALKREQs its `echo` protocol.
# lean-to-rust: the helper serves and prints its ENR; the suite binary in
# `discv5client` mode sends the same three requests.
#
# Each direction passes when the querying side exits 0, which needs a
# PONG, the target's own record in NODES, and `echo` answered with
# [1, 2, 3]. The helper builds with cargo on two cores into
# .tmp/discv5-interop/rust-target.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
out="$root/.tmp/discv5-interop"
tests="$root/.lake/build/bin/tests"
helper="$out/rust-target/release/discv5-rust"
pid=

cleanup() {
  if [[ -n "$pid" ]] && kill -0 "$pid" 2>/dev/null; then
    kill "$pid"
    wait "$pid" || true
  fi
}
trap cleanup EXIT

mkdir -p "$out"
if [[ ! -x "$helper" ]]; then
  CARGO_BUILD_JOBS=2 nice -n19 cargo build --release \
    --manifest-path "$root/scripts/discv5-rust/Cargo.toml" --target-dir "$out/rust-target"
fi
[[ -x "$tests" ]] || { echo "discv5-rust-interop: build the tests first" >&2; exit 2; }

# Wait for an `ENR <text>` line in $1 while $pid lives.
wait_enr() {
  local file=$1 enr=
  for _ in $(seq 1 100); do
    enr=$(sed -n 's/^ENR //p' "$file")
    [[ -n "$enr" ]] && { echo "$enr"; return 0; }
    kill -0 "$pid" 2>/dev/null || return 1
    sleep 0.1
  done
  return 1
}

status=0

# rust-to-lean.
LEANP2P_SUITE=discv5serve LEANP2P_DISCV5_MS=30000 LEAN_NUM_THREADS=2 \
  "$tests" >"$out/lean-serve.out" 2>"$out/lean-serve.err" &
pid=$!
enr=$(wait_enr "$out/lean-serve.out") || { echo "rust-to-lean: no ENR from the node" >&2; exit 1; }
if "$helper" query 0 "$enr" >"$out/rust-query.out" 2>"$out/rust-query.err"; then
  cat "$out/rust-query.out"
  echo "rust-to-lean: PASS"
else
  cat "$out/rust-query.out" "$out/rust-query.err"
  echo "rust-to-lean: FAIL"
  status=1
fi
cleanup
pid=

# lean-to-rust.
# The helper writes its port into its ENR before it binds, so it takes a
# fixed one (DISCV5_RUST_PORT, 30409 by default).
"$helper" serve "${DISCV5_RUST_PORT:-30409}" 30 >"$out/rust-serve.out" 2>"$out/rust-serve.err" &
pid=$!
enr=$(wait_enr "$out/rust-serve.out") || { echo "lean-to-rust: no ENR from the helper" >&2; exit 1; }
if LEANP2P_SUITE=discv5client LEANP2P_DISCV5_TARGET="$enr" LEAN_NUM_THREADS=2 \
    "$tests" >"$out/lean-query.out" 2>"$out/lean-query.err"; then
  cat "$out/lean-query.out"
  echo "lean-to-rust: PASS"
else
  cat "$out/lean-query.out" "$out/lean-query.err"
  echo "lean-to-rust: FAIL"
  status=1
fi

exit "$status"

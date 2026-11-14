#!/usr/bin/env bash
# discv5 interoperability: geth's conformance suite against our node.
#
# geth's `devp2p discv5 test` (cmd/devp2p/internal/v5test) drives ten
# protocol scenarios against a live node from two tester addresses,
# 127.0.0.1 and 127.0.0.2. Prysm's discovery is the same code:
# beacon-chain/p2p/discovery.go imports go-ethereum/p2p/discover, at
# go-ethereum v1.17.4. The pinned commit below is later than v1.17.4.
# Between the two, the discv5 protocol code changed only in metrics and
# a TALKREQ drop counter, and the test suite gained scenarios.
#
# The tool builds from a go-ethereum clone at that commit
# (DISCV5_GETH_SRC, default ../p2p/go-ethereum-discv5 beside the repo),
# with the host Go toolchain, on two cores. The node under test is the
# suite binary in `discv5serve` mode: it prints `ENR <text>` and serves
# until DISCV5_SERVE_MS passes. geth-to-lean passes when every scenario
# passes. lean-to-geth then runs a geth node (`devp2p discv5 listen`)
# and queries it from the suite binary in `discv5client` mode: PING,
# FINDNODE at distance 0, and a TALKREQ that geth answers empty.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
geth_rev=0d061403cf53263b95f9beec48f07046e78e1bed
src=${DISCV5_GETH_SRC:-"$root/../p2p/go-ethereum-discv5"}
out="$root/.tmp/discv5-interop"
tool="$out/devp2p"
tests="$root/.lake/build/bin/tests"
serve_ms=${DISCV5_SERVE_MS:-180000}
node_pid=

cleanup() {
  if [[ -n "$node_pid" ]] && kill -0 "$node_pid" 2>/dev/null; then
    kill "$node_pid"
    wait "$node_pid" || true
  fi
}
trap cleanup EXIT

mkdir -p "$out"
have=$(git -C "$src" rev-parse HEAD)
if [[ "$have" != "$geth_rev" ]]; then
  echo "discv5-geth-interop: $src is at $have, want $geth_rev" >&2
  exit 2
fi
if [[ ! -x "$tool" ]]; then
  (cd "$src" && GOFLAGS=-p=2 GOMAXPROCS=2 nice -n19 go build -o "$tool" ./cmd/devp2p)
fi
# The test binary is built here, so a run never tests a stale binary.
( cd "$root" &&
  LEAN_NUM_THREADS=2 nice -n19 taskset -c 0,1 lake build tests >"$out/lake.out" )

# The node: wait for its ENR line.
LEANP2P_SUITE=discv5serve LEANP2P_DISCV5_MS="$serve_ms" LEAN_NUM_THREADS=2 \
  "$tests" >"$out/node.out" 2>"$out/node.err" &
node_pid=$!
enr=
for _ in $(seq 1 100); do
  enr=$(sed -n 's/^ENR //p' "$out/node.out")
  [[ -n "$enr" ]] && break
  kill -0 "$node_pid" 2>/dev/null || { echo "discv5-geth-interop: the node exited" >&2; exit 1; }
  sleep 0.1
done
[[ -n "$enr" ]] || { echo "discv5-geth-interop: no ENR from the node" >&2; exit 1; }
echo "node: $enr"

# geth's suite, from both tester addresses.
status=0
if "$tool" discv5 test --listen1 127.0.0.1 --listen2 127.0.0.2 "$enr" >"$out/geth.out" 2>"$out/geth.err"; then
  grep -E -- '^-- (OK|FAIL)|tests passed' "$out/geth.out"
  echo "geth-to-lean: PASS"
else
  cat "$out/geth.out"
  echo "geth-to-lean: FAIL"
  status=1
fi
cleanup
node_pid=

# lean-to-geth: a geth node (`devp2p discv5 listen`) at a fixed endpoint,
# and the suite binary in `discv5client` mode. geth serves no `echo`, so
# the TALKREQ must get the empty answer of an unknown protocol.
geth_port=${DISCV5_GETH_PORT:-30411}
"$tool" discv5 listen --addr "127.0.0.1:$geth_port" --extaddr "127.0.0.1:$geth_port" \
  >"$out/geth-listen.out" 2>"$out/geth-listen.err" &
node_pid=$!
genr=
for _ in $(seq 1 100); do
  genr=$(grep -o -m1 'enr:[A-Za-z0-9_-]*' "$out/geth-listen.out" || true)
  [[ -n "$genr" ]] && break
  kill -0 "$node_pid" 2>/dev/null || { echo "lean-to-geth: the geth node exited" >&2; exit 1; }
  sleep 0.1
done
[[ -n "$genr" ]] || { echo "lean-to-geth: no ENR from the geth node" >&2; exit 1; }
if LEANP2P_SUITE=discv5client LEANP2P_DISCV5_TARGET="$genr" LEANP2P_DISCV5_ECHO=0 \
    LEAN_NUM_THREADS=2 "$tests" >"$out/lean-query.out" 2>"$out/lean-query.err"; then
  cat "$out/lean-query.out"
  echo "lean-to-geth: PASS"
else
  cat "$out/lean-query.out" "$out/lean-query.err"
  echo "lean-to-geth: FAIL"
  status=1
fi
exit "$status"

#!/usr/bin/env bash
# discv5 interoperability: geth's conformance suite against our node.
#
# geth's `devp2p discv5 test` (cmd/devp2p/internal/v5test) drives ten
# protocol scenarios against a live node from two tester addresses,
# 127.0.0.1 and 127.0.0.2. Prysm's discovery is the same code:
# beacon-chain/p2p/discovery.go imports go-ethereum/p2p/discover, at
# go-ethereum v1.17.4. The pinned commit below is later than v1.17.4;
# the discv5 protocol code between them changed only in metrics and a
# TALKREQ drop counter, and the test suite gained scenarios.
#
# The tool builds from a go-ethereum clone at that commit
# (DISCV5_GETH_SRC, default ../p2p/go-ethereum-discv5 beside the repo),
# with the host Go toolchain, on two cores. The node under test is the
# suite binary in `discv5serve` mode: it prints `ENR <text>` and serves
# until DISCV5_SERVE_MS passes. PASS needs every scenario to pass.
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
[[ -x "$tests" ]] || { echo "discv5-geth-interop: build the tests first" >&2; exit 2; }

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
if "$tool" discv5 test --listen1 127.0.0.1 --listen2 127.0.0.2 "$enr" >"$out/geth.out" 2>"$out/geth.err"; then
  grep -E -- '^(-- |--- )?(PASS|FAIL|ok|not ok)' "$out/geth.out" || cat "$out/geth.out"
  echo PASS
else
  cat "$out/geth.out"
  echo FAIL
  exit 1
fi

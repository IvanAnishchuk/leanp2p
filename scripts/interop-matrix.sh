#!/usr/bin/env bash
# The W5.9 gate (root PLAN W5.9; packages/cli/docs/PLAN.md, "Test
# milestones (unit 2)"): the transport-interop matrix against go-libp2p
# over tcp + /noise + yamux, plus the silent-peer and slow-reader
# scenarios, and the cells of tcp + /tls + yamux (W5.11) and quic-v1
# (W4.4). Docker appears here and nowhere else (cli ARCHITECTURE,
# "Decisions").
#
# The rust cells run sigp's rust-libp2p, the fork and the rev that
# Lighthouse pins (../p2p/sigp-rust-libp2p at accba72), through the
# test-plan peer of scripts/transport-rust. That peer builds offline
# with cargo and runs on this host, with a secp256k1 key as
# Lighthouse's. Its cells cover the stacks that Lighthouse offers:
# tcp + /noise with yamux and with mplex, and quic-v1. tcp + /tls +
# yamux runs too, for the TLS handshake.
#
# The go side is go-libp2p's own test-plan peer, built from the vendored
# tree (vendor/go-libp2p, v0.50.0) with its own PingDockerfile. Redis and
# the go containers share one docker network. The Lean `interop` binary
# runs on this host: it listens on the network's gateway address, which
# the containers reach, and it reaches Redis through a port published on
# loopback.
#
# Usage: scripts/interop-matrix.sh [out-dir]
#   LEAN_INTEROP   the harness binary (default .lake/build/bin/interop)
#   TEST_TIMEOUT   test_timeout_seconds of every run (default 60)
# The dialer lines and a results table land in out-dir (default
# .tmp/interop). The script exits nonzero when a cell fails.
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
lean=${LEAN_INTEROP:-$root/.lake/build/bin/interop}
timeout_s=${TEST_TIMEOUT:-60}
out=${1:-$root/.tmp/interop}
net=leanp2p-interop
redis=leanp2p-interop-redis
go_listener=leanp2p-interop-go-listener
go_image=leanp2p-interop-go
slow_image=leanp2p-interop-slowreader
# The unauthenticated-phase deadline of root §5.4 (Streams.unauthDeadlineMs).
unauth_s=30

mkdir -p "$out"
results="$out/results.csv"
echo "name,outcome,record" >"$results"
failed=0
lean_pid=
rust_pid=

remove_container() {
  if docker container inspect "$1" >/dev/null 2>/dev/null; then
    docker rm -f "$1" >/dev/null
  fi
}

cleanup() {
  if [ -n "$lean_pid" ]; then kill "$lean_pid" 2>/dev/null || true; fi
  if [ -n "$rust_pid" ]; then kill "$rust_pid" 2>/dev/null || true; fi
  remove_container "$go_listener"
  remove_container "$redis"
  if docker network inspect "$net" >/dev/null 2>/dev/null; then
    docker network rm "$net" >/dev/null
  fi
}
trap cleanup EXIT

# The harness is built here unless LEAN_INTEROP names one, so a run never
# tests a stale binary.
if [ -z "${LEAN_INTEROP:-}" ]; then
  ( cd "$root" &&
    LEAN_NUM_THREADS=2 nice -n19 taskset -c 0,1 lake build interop >"$out/lake.out" )
fi
[ -x "$lean" ] || { echo "interop-matrix: no harness at $lean" >&2; exit 2; }

echo "building the go peers (vendor/go-libp2p $(cat "$root/vendor/go-libp2p/.pin"))" >&2
docker build -q -t "$go_image" -f "$root/vendor/go-libp2p/test-plans/PingDockerfile" \
  "$root/vendor/go-libp2p" >/dev/null
docker build -q -t "$slow_image" -f "$root/scripts/interop-slowreader/Dockerfile" \
  --build-context slowreader="$root/scripts/interop-slowreader" "$root/vendor/go-libp2p" >/dev/null

sigp_rev=accba72bb4eafc692ac518339ef2c4080b6f8461
have=$(git -C "$root/../p2p/sigp-rust-libp2p" rev-parse HEAD)
if [ "$have" != "$sigp_rev" ]; then
  echo "interop-matrix: ../p2p/sigp-rust-libp2p is at $have, want $sigp_rev" >&2
  exit 2
fi
echo "building the rust peer (sigp rust-libp2p ${sigp_rev:0:7})" >&2
CARGO_BUILD_JOBS=2 nice -n19 cargo build -q --offline --release \
  --manifest-path "$root/scripts/transport-rust/Cargo.toml" \
  --target-dir "$root/.tmp/transport-rust/target"
rust="$root/.tmp/transport-rust/target/release/transport-rust"

cleanup
docker network create "$net" >/dev/null
gateway=$(docker network inspect -f '{{(index .IPAM.Config 0).Gateway}}' "$net")
docker run -d --rm --name "$redis" --network "$net" -p 127.0.0.1::6379 redis:7-alpine >/dev/null
redis_host=$(docker port "$redis" 6379/tcp)
# The readiness wait has a bound, like every wait in this script: a
# server that never answers PING fails the run, and the script exits
# instead of hanging CI.
waited=0
until docker exec "$redis" redis-cli PING >/dev/null 2>/dev/null; do
  [ "$waited" -lt 100 ] || { echo "interop-matrix: redis did not answer PING" >&2; exit 2; }
  sleep 0.1
  waited=$((waited + 1))
done

# The stack of the cell that runs: the test plan's transport, security,
# and muxer. `cell` sets them; the silent peer and the slow reader run
# on the gate's stack. quic-v1 ignores the security and the muxer, as
# both peers do.
transport=tcp
security=noise
muxer=yamux

# The test plan's variables, for one side. $1 is_dialer, $2 redis_addr.
plan_env() {
  echo "transport=$transport muxer=$muxer security=$security is_dialer=$1 redis_addr=$2 test_timeout_seconds=$timeout_s"
}

start_lean_listener() {
  # shellcheck disable=SC2046  # the words of plan_env are the variables
  env $(plan_env false "$redis_host") ip="$gateway" "$lean" 2>"$out/$1.listener.log" &
  lean_pid=$!
}

start_go_listener() {
  docker run -d --rm --name "$go_listener" --network "$net" \
    -e transport="$transport" -e muxer="$muxer" -e security="$security" -e is_dialer=false \
    -e redis_addr="$redis:6379" -e test_timeout_seconds="$timeout_s" "$go_image" >/dev/null
}

# The rust peer runs on this host and listens on loopback, which the
# Lean dialer on this host reaches.
start_rust_listener() {
  # shellcheck disable=SC2046
  env $(plan_env false "$redis_host") ip=127.0.0.1 "$rust" 2>"$out/$1.listener.log" &
  rust_pid=$!
}

stop_listeners() {
  if [ -n "$lean_pid" ]; then kill "$lean_pid" 2>/dev/null || true; wait "$lean_pid" 2>/dev/null || true; lean_pid=; fi
  if [ -n "$rust_pid" ]; then kill "$rust_pid" 2>/dev/null || true; wait "$rust_pid" 2>/dev/null || true; rust_pid=; fi
  remove_container "$go_listener"
}

run_lean_dialer() {
  # shellcheck disable=SC2046
  timeout $((timeout_s + 10)) env $(plan_env true "$redis_host") "$lean" >"$out/$1.json" 2>"$out/$1.dialer.log"
}

run_go_dialer() {
  timeout $((timeout_s + 10)) docker run --rm --network "$net" \
    -e transport="$transport" -e muxer="$muxer" -e security="$security" -e is_dialer=true \
    -e redis_addr="$redis:6379" -e test_timeout_seconds="$timeout_s" "$go_image" \
    >"$out/$1.json" 2>"$out/$1.dialer.log"
}

run_rust_dialer() {
  # shellcheck disable=SC2046
  timeout $((timeout_s + 10)) env $(plan_env true "$redis_host") "$rust" >"$out/$1.json" 2>"$out/$1.dialer.log"
}

# One CSV field: the value in double quotes, each inner quote doubled.
csv() { local v=${1//\"/\"\"}; printf '"%s"' "$v"; }

# Record one result. $1 the file stem, $2 the name, $3 the exit status,
# then the JSON keys the output line must carry. A pass needs exit 0
# and every key.
record_result() {
  local file=$1 name=$2 status=$3 line='' key ok=1 outcome=success
  shift 3
  [ "$status" = 0 ] || ok=0
  [ -s "$out/$file.json" ] && line=$(tr -d '\n' <"$out/$file.json")
  for key in "$@"; do [[ $line == *"\"$key\""* ]] || ok=0; done
  if [ "$ok" = 1 ]; then
    echo "PASS $name $line" >&2
  else
    outcome=failure
    echo "FAIL $name (exit $status; see $out/$file.*.log)" >&2
    failed=$((failed + 1))
  fi
  echo "$(csv "$name"),$outcome,$(csv "$line")" >>"$results"
}

# One cell of the matrix: $1 dialer (lean|go|rust), $2 listener (lean|go|rust),
# $3 the transport, $4 the security, $5 the muxer (the gate's stack when
# absent).
cell() {
  transport=${3:-tcp} security=${4:-noise} muxer=${5:-yamux}
  local stack="$transport, $security, $muxer"
  [ "$transport" = quic-v1 ] && stack=quic-v1
  local file="$1-x-$2-${stack//, /-}" status=0
  docker exec "$redis" redis-cli FLUSHALL >/dev/null
  "start_$2_listener" "$file"
  "run_$1_dialer" "$file" || status=$?
  stop_listeners
  record_result "$file" "$1 x $2 ($stack)" "$status" handshakePlusOneRTTMillis pingRTTMilllis
  transport=tcp security=noise muxer=yamux
}

# The listener's published address, once it is in Redis.
published_addr() {
  local addr='' waited=0
  while [ -z "$addr" ] && [ "$waited" -lt $((timeout_s * 10)) ]; do
    addr=$(docker exec "$redis" redis-cli LINDEX listenerAddr 0)
    [ -n "$addr" ] || { sleep 0.1; waited=$((waited + 1)); }
  done
  echo "$addr"
}

# The silent peer (PRINCIPLES 5.4): a raw TCP connection that sends
# nothing. The Lean listener must close it at the deadline of §5.4, and a
# go dialer must pass meanwhile.
silent_peer() {
  local name=silent-peer status=0 addr ip port start elapsed
  docker exec "$redis" redis-cli FLUSHALL >/dev/null
  start_lean_listener "$name"
  addr=$(published_addr)
  if [ -z "$addr" ]; then
    echo "$name: the Lean listener published no address" >&2
    stop_listeners
    record_result "$name" "$name" 1
    return
  fi
  IFS=/ read -r _ _ ip _ port _ <<<"$addr"
  start=$(date +%s)
  # The client keeps its write side open, sends nothing, and reads until
  # the listener closes the connection. The inner shell expands $0 and
  # $1, so the single quotes are deliberate.
  # shellcheck disable=SC2016
  timeout $((unauth_s + 15)) bash -c 'exec 3<>"/dev/tcp/$0/$1"; cat <&3 >/dev/null' "$ip" "$port" &
  local silent=$!
  run_go_dialer "$name" || status=$?
  local silent_status=0
  wait "$silent" || silent_status=$?
  elapsed=$(( $(date +%s) - start ))
  stop_listeners
  if [ "$silent_status" != 0 ] || [ "$elapsed" -lt $((unauth_s - 2)) ]; then
    echo "$name: the silent connection ended with $silent_status after ${elapsed}s" >&2
    status=1
  else
    echo "$name: the silent connection closed after ${elapsed}s" >&2
  fi
  record_result "$name" "$name" "$status" handshakePlusOneRTTMillis pingRTTMilllis
}

# The slow reader: a go peer that writes on a ping stream and never reads
# the echoes (scripts/interop-slowreader/main.go).
slow_reader() {
  local name=slow-reader status=0
  docker exec "$redis" redis-cli FLUSHALL >/dev/null
  start_lean_listener "$name"
  timeout $((timeout_s + 10)) docker run --rm --network "$net" \
    -e redis_addr="$redis:6379" -e test_timeout_seconds="$timeout_s" "$slow_image" \
    >"$out/$name.json" 2>"$out/$name.dialer.log" || status=$?
  stop_listeners
  record_result "$name" "$name" "$status" stalledAfterBytes pingRTTMillis
}

# The go x go cell checks the setup itself. The gate's stack first, then
# TLS over TCP (root PLAN W5.11), then QUIC (root PLAN W4.4). mplex has
# no go cell: go-libp2p v0.50 removed it.
cell go go
cell lean go
cell go lean
cell lean lean
cell lean go tcp tls yamux
cell go lean tcp tls yamux
cell lean lean tcp tls yamux
cell go go quic-v1
cell lean go quic-v1
cell go lean quic-v1
cell lean lean quic-v1
# The rust x rust cells check the setup, as go x go does.
cell rust rust
cell lean rust
cell rust lean
cell rust rust tcp noise mplex
cell lean rust tcp noise mplex
cell rust lean tcp noise mplex
cell lean rust tcp tls yamux
cell rust lean tcp tls yamux
cell rust rust quic-v1
cell lean rust quic-v1
cell rust lean quic-v1
silent_peer
slow_reader

echo "$failed failed; results in $results" >&2
[ "$failed" = 0 ]

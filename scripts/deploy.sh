#!/usr/bin/env bash
# deploy.sh — Sync local source changes to the Hetzner fleet and rebuild binaries.
#
# Rsyncs crates/, Cargo.toml, Cargo.lock, and helper scripts to every node,
# then rebuilds reasonmesh-cli in release mode on each machine in parallel.
#
# Run after provision.sh whenever local source has changed and needs to be
# deployed to the running fleet (e.g. after performance fixes, before benchmarks).
#
# Usage:
#   source scripts/env.sh
#   ./scripts/deploy.sh

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

ENV_FILE="$SCRIPT_DIR/env.sh"
[[ -f "$ENV_FILE" ]] || { echo "error: scripts/env.sh not found — run provision.sh first" >&2; exit 1; }
# shellcheck disable=SC1090
source "$ENV_FILE"

for v in RM_SSH_KEY RM_BENCH_IP RM_NODE1_IP RM_NODE2_IP RM_NODE3_IP RM_NODE4_IP; do
  [[ -n "${!v:-}" ]] || { echo "error: $v not set in env.sh" >&2; exit 1; }
done

GREEN='\033[0;32m'; CYAN='\033[0;36m'; YELLOW='\033[1;33m'; RED='\033[0;31m'; NC='\033[0m'
ts()   { date +%H:%M:%S; }
log()  { echo -e "${GREEN}[$(ts) deploy]${NC} $*"; }
step() { echo -e "\n${CYAN}[$(ts)] ── $* ──${NC}"; }
warn() { echo -e "${YELLOW}[$(ts) warn]${NC}  $*" >&2; }
die()  { echo -e "${RED}[$(ts) error]${NC} $*" >&2; exit 1; }

SSH_OPTS="-i $RM_SSH_KEY -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR -o ConnectTimeout=20 -o ServerAliveInterval=15 -o ServerAliveCountMax=8"
REMOTE_ROOT="/opt/reasonmesh"

rsync_source() {
  local host=$1
  local label=$2
  log "  [rsync:start] $label ($host)"
  rsync -az --delete \
    -e "ssh $SSH_OPTS" \
    --exclude "target/" \
    --exclude ".git/" \
    --exclude "benchmarks/" \
    --exclude "experiments/" \
    --exclude "docs/" \
    --exclude "tla/" \
    --exclude "fuzz/" \
    --exclude "tests/" \
    --exclude "scripts/" \
    "$REPO_ROOT/" \
    "root@$host:$REMOTE_ROOT/"
  log "  [rsync:done ] $label"
}

build_remote() {
  local host=$1
  local label=$2
  log "  [build:start] $label ($host) — incremental, typically 1-3 min"
  ssh $SSH_OPTS "root@$host" \
    "cd $REMOTE_ROOT && \
     export PATH=\"\$HOME/.cargo/bin:\$PATH\" && \
     cargo build --release -p reasonmesh-cli 2>&1 | tail -3 && \
     ln -sf $REMOTE_ROOT/target/release/reasonmesh /usr/local/bin/reasonmesh && \
     echo '  → ' \$(reasonmesh --version 2>/dev/null || echo 'built OK')"
  log "  [build:done ] $label"
}

# ── 1. Sync source to all nodes in parallel ────────────────────────────────────
step "1/3  rsync source → all nodes (parallel)"
log "Starting rsync to rm-bench + rm-node1..4 at $(ts)"

# Indexed arrays — compatible with Bash 3.2 on macOS (no declare -A)
RSYNC_NAMES=(rm-bench rm-node1 rm-node2 rm-node3 rm-node4)
RSYNC_IPS=("$RM_BENCH_IP" "$RM_NODE1_IP" "$RM_NODE2_IP" "$RM_NODE3_IP" "$RM_NODE4_IP")
RSYNC_PIDS=()
for i in "${!RSYNC_NAMES[@]}"; do
  rsync_source "${RSYNC_IPS[$i]}" "${RSYNC_NAMES[$i]}" & RSYNC_PIDS+=($!)
done
for i in "${!RSYNC_PIDS[@]}"; do
  wait "${RSYNC_PIDS[$i]}" || warn "rsync failed on ${RSYNC_NAMES[$i]}"
done
log "Source sync complete at $(ts)"

# ── 2. Sync local/ data to rm-bench + benchmarks/ to nodes ───────────────────
step "2/3  rsync benchmarks/ + experiments/ → rm-bench + all nodes"
log "Syncing local data at $(ts)"
rsync -az -e "ssh $SSH_OPTS" \
  "$REPO_ROOT/benchmarks/" \
  "$REPO_ROOT/experiments/" \
  "$REPO_ROOT/scripts/run-per-problem.py" \
  "root@$RM_BENCH_IP:$REMOTE_ROOT/local/" &
for n in 1 2 3 4; do
  ip_var="RM_NODE${n}_IP"
  rsync -az -e "ssh $SSH_OPTS" \
    "$REPO_ROOT/benchmarks/" \
    "root@${!ip_var}:$REMOTE_ROOT/benchmarks/" &
done
wait
log "Local data sync complete at $(ts)"

# ── 3. Rebuild on all nodes in parallel ────────────────────────────────────────
step "3/3  cargo build --release on all nodes (parallel)"
log "Starting builds at $(ts)"

BUILD_NAMES=(rm-bench rm-node1 rm-node2 rm-node3 rm-node4)
BUILD_IPS=("$RM_BENCH_IP" "$RM_NODE1_IP" "$RM_NODE2_IP" "$RM_NODE3_IP" "$RM_NODE4_IP")
BUILD_PIDS=()
for i in "${!BUILD_NAMES[@]}"; do
  build_remote "${BUILD_IPS[$i]}" "${BUILD_NAMES[$i]}" & BUILD_PIDS+=($!)
done
for i in "${!BUILD_PIDS[@]}"; do
  wait "${BUILD_PIDS[$i]}" || warn "build failed on ${BUILD_NAMES[$i]}"
done

log "Deploy complete at $(ts) — all nodes running latest binary"

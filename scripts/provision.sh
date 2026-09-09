#!/usr/bin/env bash
# provision.sh — create 5 Hetzner VMs and set up the ReasonMesh benchmark environment
#
# Fleet:
#   rm-bench        CPX62  (16 shared vCPU, 32 GB)  single-node scaling study
#   rm-node1..4     CPX32  ( 8 shared vCPU, 16 GB)  4-node distributed experiment
#
# Prerequisites:
#   brew install hcloud        (macOS)
#   hcloud context create bench   (paste your API token when prompted)
#
# Usage:
#   ./scripts/provision.sh
#
# Writes scripts/env.sh with IP addresses and the SSH key path.
# Source that file before running run-benchmarks.sh or collect.sh.

set -euo pipefail

START_SECONDS=$SECONDS

# ── Configuration ─────────────────────────────────────────────────────────────
LOCATION="nbg1"               # Nuremberg — all machines in same DC for low latency
IMAGE="ubuntu-24.04"
BENCH_TYPE="${BENCH_TYPE:-cpx62}"   # override: BENCH_TYPE=cpx52 ./scripts/provision.sh
NODE_TYPE="${NODE_TYPE:-cpx32}"     # override: NODE_TYPE=cpx22 ./scripts/provision.sh
NETWORK_NAME="reasonmesh-net"
NETWORK_RANGE="10.0.1.0/24"
BENCH_SERVER="rm-bench"
NODE_SERVERS=(rm-node1 rm-node2 rm-node3 rm-node4)
PRIVATE_IPS=(10.0.1.10 10.0.1.21 10.0.1.22 10.0.1.23 10.0.1.24)
SSH_KEY_FILE="$HOME/.ssh/reasonmesh_bench"
# Key name gets a date suffix so re-runs don't collide
SSH_KEY_NAME="reasonmesh-bench-$(date +%Y%m%d)"

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"

# ── Helpers ───────────────────────────────────────────────────────────────────
RED='\033[0;31m'; GREEN='\033[0;32m'; YELLOW='\033[1;33m'; CYAN='\033[0;36m'; BOLD='\033[1m'; NC='\033[0m'
ts()      { date +%H:%M:%S; }
elapsed() { echo "$((SECONDS - START_SECONDS))s"; }
log()     { echo -e "${GREEN}[$(ts) provision]${NC} $*"; }
step()    { echo -e "\n${CYAN}${BOLD}[$(ts)] ── $* ──${NC}"; }
warn()    { echo -e "${YELLOW}[$(ts) warn]${NC} $*"; }
die()     { echo -e "${RED}[$(ts) error]${NC} $*" >&2; exit 1; }

get_public_ip() {
  hcloud server describe "$1" -o json \
    | python3 -c "import sys,json; print(json.load(sys.stdin)['public_net']['ipv4']['ip'])"
}

wait_for_ssh() {
  local host=$1 label=$2
  local attempts=0 max=36  # 36 × 10s = 6 minutes
  log "Waiting for SSH on $label ($host) — polling every 10s (max 6 min)"
  until ssh -i "$SSH_KEY_FILE" \
            -o StrictHostKeyChecking=no \
            -o UserKnownHostsFile=/dev/null \
            -o LogLevel=ERROR \
            -o ConnectTimeout=5 \
            -o BatchMode=yes \
            "root@$host" true 2>/dev/null; do
    attempts=$((attempts + 1))
    [[ $attempts -ge $max ]] && die "Timed out waiting for SSH on $label after $((attempts * 10))s"
    log "  ... attempt $attempts/$max (${label} not ready yet)"
    sleep 10
  done
  log "  SSH ready on $label after $((attempts * 10))s"
}

ssh_exec() {
  local host=$1; shift
  ssh -i "$SSH_KEY_FILE" \
      -o StrictHostKeyChecking=no \
      -o UserKnownHostsFile=/dev/null \
      -o LogLevel=ERROR \
      -o BatchMode=yes \
      -o ServerAliveInterval=30 \
      -o ServerAliveCountMax=6 \
      "root@$host" "$@"
}

# ── 1. Preflight checks ───────────────────────────────────────────────────────
step "1/9  Preflight checks"
command -v hcloud   >/dev/null 2>&1 || die "hcloud not found — install with: brew install hcloud"
command -v python3  >/dev/null 2>&1 || die "python3 not found"
hcloud context list | grep -q '\*' || die "No active hcloud context — run: hcloud context create bench"

log "Preflight OK — location=$LOCATION, bench=$BENCH_TYPE, nodes=$NODE_TYPE ×${#NODE_SERVERS[@]}"

# ── 2. SSH key ────────────────────────────────────────────────────────────────
step "2/9  SSH key"
if [[ ! -f "$SSH_KEY_FILE" ]]; then
  log "Generating SSH key pair at $SSH_KEY_FILE"
  ssh-keygen -t ed25519 -f "$SSH_KEY_FILE" -N "" -C "reasonmesh-bench"
fi

if ! hcloud ssh-key list -o columns=name | grep -qF "$SSH_KEY_NAME"; then
  log "Uploading public key to Hetzner as '$SSH_KEY_NAME'"
  hcloud ssh-key create --name "$SSH_KEY_NAME" \
    --public-key "$(cat "${SSH_KEY_FILE}.pub")"
else
  log "SSH key '$SSH_KEY_NAME' already exists in Hetzner — reusing"
fi

# ── 3. Private network ────────────────────────────────────────────────────────
step "3/9  Private network"
if ! hcloud network list -o columns=name | grep -qF "$NETWORK_NAME"; then
  log "Creating private network '$NETWORK_NAME' ($NETWORK_RANGE)"
  hcloud network create --name "$NETWORK_NAME" --ip-range "$NETWORK_RANGE"
  hcloud network add-subnet "$NETWORK_NAME" \
    --type server \
    --network-zone eu-central \
    --ip-range "$NETWORK_RANGE"
  log "Network created"
else
  log "Network '$NETWORK_NAME' already exists — reusing"
fi

# ── 4. Create benchmark machine ───────────────────────────────────────────────
step "4/9  Create rm-bench ($BENCH_TYPE)"
if ! hcloud server list -o columns=name | grep -qF "$BENCH_SERVER"; then
  log "Creating '$BENCH_SERVER' ($BENCH_TYPE, image=$IMAGE, location=$LOCATION)…"
  hcloud server create \
    --name "$BENCH_SERVER" \
    --type "$BENCH_TYPE" \
    --image "$IMAGE" \
    --location "$LOCATION" \
    --ssh-key "$SSH_KEY_NAME"
  log "Attaching to private network — ip=${PRIVATE_IPS[0]}"
  hcloud server attach-to-network "$BENCH_SERVER" \
    --network "$NETWORK_NAME" \
    --ip "${PRIVATE_IPS[0]}"
  log "rm-bench created  [$(elapsed) total]"
else
  log "'$BENCH_SERVER' already exists — skipping creation"
fi

# ── 5. Create distributed nodes ───────────────────────────────────────────────
step "5/9  Create rm-node1..4 ($NODE_TYPE × 4)"
for i in "${!NODE_SERVERS[@]}"; do
  name="${NODE_SERVERS[$i]}"
  priv_ip="${PRIVATE_IPS[$((i + 1))]}"
  if ! hcloud server list -o columns=name | grep -qF "$name"; then
    log "Creating '$name' ($NODE_TYPE, private=$priv_ip)…"
    hcloud server create \
      --name "$name" \
      --type "$NODE_TYPE" \
      --image "$IMAGE" \
      --location "$LOCATION" \
      --ssh-key "$SSH_KEY_NAME"
    hcloud server attach-to-network "$name" \
      --network "$NETWORK_NAME" \
      --ip "$priv_ip"
    log "$name created"
  else
    log "'$name' already exists — skipping creation"
  fi
done
log "All servers created  [$(elapsed) total]"

# ── 6. Collect public IPs and wait for SSH ────────────────────────────────────
step "6/9  Wait for SSH on all nodes"
log "Collecting public IPs…"
BENCH_IP=$(get_public_ip "$BENCH_SERVER")
log "  rm-bench   public=$BENCH_IP  private=${PRIVATE_IPS[0]}"

NODE_PUBLIC_IPS=()
for i in "${!NODE_SERVERS[@]}"; do
  ip=$(get_public_ip "${NODE_SERVERS[$i]}")
  NODE_PUBLIC_IPS+=("$ip")
  log "  ${NODE_SERVERS[$i]}  public=$ip  private=${PRIVATE_IPS[$((i + 1))]}"
done

wait_for_ssh "$BENCH_IP" "rm-bench"
for i in "${!NODE_SERVERS[@]}"; do
  wait_for_ssh "${NODE_PUBLIC_IPS[$i]}" "${NODE_SERVERS[$i]}"
done
log "All nodes SSH-ready"

# ── 7. Run setup on all machines in parallel ──────────────────────────────────
step "7/9  remote-setup.sh on all 5 nodes in parallel (~25 min)"
log "Each node streams to its own log file below. Watch any with tail -f."
log "  rm-bench : /tmp/setup-rm-bench.log"
for name in "${NODE_SERVERS[@]}"; do
  log "  $name : /tmp/setup-${name}.log"
done
log ""

# Start all setups in parallel, each piped to its own log file
declare -a SETUP_PIDS SETUP_NAMES

> /tmp/setup-rm-bench.log
log "  [rm-bench] starting (bench role)…"
ssh_exec "$BENCH_IP" bash -s -- bench \
  < "$SCRIPT_DIR/remote-setup.sh" >> /tmp/setup-rm-bench.log 2>&1 &
SETUP_PIDS+=($!)
SETUP_NAMES+=("rm-bench")

for i in "${!NODE_SERVERS[@]}"; do
  name="${NODE_SERVERS[$i]}"
  > /tmp/setup-${name}.log
  log "  [$name] starting (node role)…"
  ssh_exec "${NODE_PUBLIC_IPS[$i]}" bash -s -- node \
    < "$SCRIPT_DIR/remote-setup.sh" >> /tmp/setup-${name}.log 2>&1 &
  SETUP_PIDS+=($!)
  SETUP_NAMES+=("$name")
done

log "All 5 setups running. Polling every 30s for progress…"

# Poll every 30s: show last log line from still-running nodes; report completions.
# Uses plain indexed arrays (compatible with Bash 3.2 on macOS — no declare -A).
SETUP_OK=1
n_total=${#SETUP_PIDS[@]}
n_done=0
# SETUP_DONE[i]=1 when node i has finished; 0 while still running
SETUP_DONE=()
for i in "${!SETUP_PIDS[@]}"; do SETUP_DONE[$i]=0; done

poll=0
while [[ $n_done -lt $n_total ]]; do
  sleep 30; poll=$((poll + 30))
  for i in "${!SETUP_PIDS[@]}"; do
    [[ "${SETUP_DONE[$i]}" == "1" ]] && continue
    pid="${SETUP_PIDS[$i]}"
    name="${SETUP_NAMES[$i]}"
    if ! kill -0 "$pid" 2>/dev/null; then
      if wait "$pid" 2>/dev/null; then
        log "  ✓ $name  DONE  [${poll}s / $(elapsed) total]"
      else
        warn "  ✗ $name  FAILED  [${poll}s] — tail /tmp/setup-${name}.log for details"
        SETUP_OK=0
      fi
      SETUP_DONE[$i]=1
      n_done=$((n_done + 1))
    else
      last=$(grep -v '^$' "/tmp/setup-${name}.log" 2>/dev/null | tail -1 || echo "…")
      log "  · $name [${poll}s]: $last"
    fi
  done
done

[[ $SETUP_OK -eq 1 ]] \
  && log "All nodes setup complete  [$(elapsed) total]" \
  || warn "One or more setup runs failed — check /tmp/setup-<node>.log"

# ── 8. Upload benchmark data + scripts to rm-bench ────────────────────────────
step "8/9  Upload benchmark data to rm-bench"
log "Uploading benchmarks/, experiments/, run-per-problem.py…"
rsync -az --progress \
  -e "ssh -i $SSH_KEY_FILE -o StrictHostKeyChecking=no -o UserKnownHostsFile=/dev/null -o LogLevel=ERROR -o ServerAliveInterval=15" \
  "$REPO_ROOT/benchmarks/" \
  "$REPO_ROOT/experiments/" \
  "$REPO_ROOT/scripts/run-per-problem.py" \
  "root@$BENCH_IP:/opt/reasonmesh/local/"
log "Upload complete  [$(elapsed) total]"

# ── 8b. Establish cluster SSH key: rm-bench → nodes ──────────────────────────
# Generates a dedicated key on rm-bench so the benchmark runner can start
# distributed experiments without needing the main external private key on-server.
step "8b/9  Cluster SSH key (rm-bench → nodes)"
CLUSTER_PUB=$(ssh_exec "$BENCH_IP" bash -s <<'KEYSCRIPT'
set -euo pipefail
KEY="/root/.ssh/rm_cluster"
if [[ ! -f "$KEY" ]]; then
  ssh-keygen -t ed25519 -f "$KEY" -N "" -C "rm-bench-cluster" >/dev/null
fi
cat "${KEY}.pub"
KEYSCRIPT
)
log "  rm-bench cluster pubkey: ${CLUSTER_PUB:0:60}..."
for i in "${!NODE_SERVERS[@]}"; do
  ssh_exec "${NODE_PUBLIC_IPS[$i]}" \
    "grep -qF '$CLUSTER_PUB' /root/.ssh/authorized_keys 2>/dev/null || \
     echo '$CLUSTER_PUB' >> /root/.ssh/authorized_keys"
  log "  cluster key added to ${NODE_SERVERS[$i]}"
done
log "Cluster key distributed  [$(elapsed) total]"

# ── 9. Write env.sh ───────────────────────────────────────────────────────────
step "9/9  Write scripts/env.sh"
ENV_FILE="$SCRIPT_DIR/env.sh"
cat > "$ENV_FILE" <<EOF
# Auto-generated by provision.sh on $(date -u +%Y-%m-%dT%H:%M:%SZ)
# Source this file before running run-benchmarks.sh or collect.sh:
#   source scripts/env.sh
export RM_SSH_KEY="$SSH_KEY_FILE"
export RM_SSH_KEY_NAME="$SSH_KEY_NAME"
export RM_NETWORK_NAME="$NETWORK_NAME"

# rm-bench (${BENCH_TYPE} — single-node scaling study)
export RM_BENCH_IP="$BENCH_IP"
export RM_BENCH_PRIV="${PRIVATE_IPS[0]}"

# rm-node1..4 (${NODE_TYPE} — distributed experiment)
export RM_NODE1_IP="${NODE_PUBLIC_IPS[0]}"
export RM_NODE2_IP="${NODE_PUBLIC_IPS[1]}"
export RM_NODE3_IP="${NODE_PUBLIC_IPS[2]}"
export RM_NODE4_IP="${NODE_PUBLIC_IPS[3]}"
export RM_NODE1_PRIV="${PRIVATE_IPS[1]}"
export RM_NODE2_PRIV="${PRIVATE_IPS[2]}"
export RM_NODE3_PRIV="${PRIVATE_IPS[3]}"
export RM_NODE4_PRIV="${PRIVATE_IPS[4]}"
EOF
log "Wrote $ENV_FILE"

# ── Done ──────────────────────────────────────────────────────────────────────
echo ""
log "════════════════════════════════════════════"
log "Provisioning complete in $(elapsed)"
log "════════════════════════════════════════════"
log ""
log "Fleet:"
log "  rm-bench  $BENCH_IP   ($BENCH_TYPE — single-node scaling)"
for i in "${!NODE_SERVERS[@]}"; do
  log "  ${NODE_SERVERS[$i]}  ${NODE_PUBLIC_IPS[$i]}  ($NODE_TYPE — distributed)"
done
log ""
log "Next steps:"
log "  source scripts/env.sh"
log "  ./scripts/run-benchmarks.sh      # runs all experiments (~2-3 hours)"
log "  ./scripts/collect.sh             # pulls results to experiments/data/"
log "  ./scripts/teardown.sh            # destroys all VMs when done"

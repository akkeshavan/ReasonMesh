#!/usr/bin/env bash
# teardown.sh — destroy all Hetzner VMs and clean up cloud resources
#
# Usage:
#   source scripts/env.sh
#   ./scripts/teardown.sh
#
# This deletes: rm-bench, rm-node1..4, the SSH key from Hetzner, and the
# private network. The local SSH key pair (~/.ssh/reasonmesh_bench) and
# scripts/env.sh are left in place.
#
# IMPORTANT: run collect.sh first if you haven't already pulled results.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ENV_FILE="$SCRIPT_DIR/env.sh"

GREEN='\033[0;32m'; YELLOW='\033[1;33m'; RED='\033[0;31m'; NC='\033[0m'
log()  { echo -e "${GREEN}[teardown]${NC} $*"; }
warn() { echo -e "${YELLOW}[warn]${NC} $*"; }

# ── Source env for key name and network name ───────────────────────────────────
if [[ -f "$ENV_FILE" ]]; then
  # shellcheck disable=SC1090
  source "$ENV_FILE"
else
  warn "scripts/env.sh not found — will use default names"
  RM_SSH_KEY_NAME=""
  RM_NETWORK_NAME="reasonmesh-net"
fi

# ── Safety confirmation ────────────────────────────────────────────────────────
echo -e "${RED}This will permanently delete the following Hetzner resources:${NC}"
echo "  Servers: rm-bench rm-node1 rm-node2 rm-node3 rm-node4"
echo "  Network: ${RM_NETWORK_NAME:-reasonmesh-net}"
[[ -n "${RM_SSH_KEY_NAME:-}" ]] && echo "  SSH key: $RM_SSH_KEY_NAME"
echo ""
read -r -p "Type 'yes' to confirm: " confirm
[[ "$confirm" == "yes" ]] || { echo "Aborted."; exit 0; }

# ── Delete servers ─────────────────────────────────────────────────────────────
for name in rm-bench rm-node1 rm-node2 rm-node3 rm-node4; do
  if hcloud server list -o columns=name | grep -qF "$name"; then
    log "Deleting server '$name'…"
    hcloud server delete "$name"
  else
    warn "Server '$name' not found — skipping"
  fi
done

# ── Delete network ────────────────────────────────────────────────────────────
NETWORK="${RM_NETWORK_NAME:-reasonmesh-net}"
if hcloud network list -o columns=name | grep -qF "$NETWORK"; then
  log "Deleting network '$NETWORK'…"
  hcloud network delete "$NETWORK"
else
  warn "Network '$NETWORK' not found — skipping"
fi

# ── Delete SSH key from Hetzner ───────────────────────────────────────────────
if [[ -n "${RM_SSH_KEY_NAME:-}" ]]; then
  if hcloud ssh-key list -o columns=name | grep -qF "$RM_SSH_KEY_NAME"; then
    log "Deleting SSH key '$RM_SSH_KEY_NAME' from Hetzner…"
    hcloud ssh-key delete "$RM_SSH_KEY_NAME"
  else
    warn "SSH key '$RM_SSH_KEY_NAME' not found in Hetzner — skipping"
  fi
fi

log "Teardown complete. Local files kept:"
log "  $HOME/.ssh/reasonmesh_bench{,.pub}  — local key pair"
log "  scripts/env.sh                       — IP record"
log "  experiments/data/                    — collected results"

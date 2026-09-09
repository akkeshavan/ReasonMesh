#!/usr/bin/env bash
# collect.sh — pull benchmark results from rm-bench back to experiments/data/
#
# Usage:
#   source scripts/env.sh
#   ./scripts/collect.sh
#
# Rsyncs experiments/data/ from rm-bench into the local experiments/data/
# directory. Safe to run multiple times — rsync only transfers changed files.
# Run this before teardown.sh.

set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
REPO_ROOT="$(cd "$SCRIPT_DIR/.." && pwd)"
ENV_FILE="$SCRIPT_DIR/env.sh"

GREEN='\033[0;32m'; RED='\033[0;31m'; NC='\033[0m'
log() { echo -e "${GREEN}[collect]${NC} $*"; }
die() { echo -e "${RED}[error]${NC} $*" >&2; exit 1; }

# ── Load env ──────────────────────────────────────────────────────────────────
[[ -f "$ENV_FILE" ]] || die "scripts/env.sh not found — run provision.sh first"
# shellcheck disable=SC1090
source "$ENV_FILE"

[[ -n "${RM_BENCH_IP:-}" ]]   || die "RM_BENCH_IP not set in env.sh"
[[ -n "${RM_SSH_KEY:-}" ]]    || die "RM_SSH_KEY not set in env.sh"
[[ -f "$RM_SSH_KEY" ]]        || die "SSH key not found at $RM_SSH_KEY"

# ── Pull results ───────────────────────────────────────────────────────────────
REMOTE_DATA="/opt/reasonmesh/local/results"
LOCAL_DATA="$REPO_ROOT/experiments/data"

log "Pulling results from rm-bench ($RM_BENCH_IP) → experiments/data/"
rsync -az --progress \
  -e "ssh -i $RM_SSH_KEY -o StrictHostKeyChecking=no" \
  "root@$RM_BENCH_IP:$REMOTE_DATA/" \
  "$LOCAL_DATA/"

# ── Summary ───────────────────────────────────────────────────────────────────
log "Done. Local results:"
find "$LOCAL_DATA" -name '*.json' -newer "$ENV_FILE" \
  | sort \
  | while read -r f; do
      size=$(wc -c < "$f")
      echo "  $f  (${size} bytes)"
    done

log ""
log "Run analysis:"
log "  python3 experiments/analyze_g2.py        # G2 scaling table"
log "  python3 experiments/analyze_g3.py        # G3 vs baselines"
log "  python3 experiments/analyze_distributed.py  # G4 distributed"

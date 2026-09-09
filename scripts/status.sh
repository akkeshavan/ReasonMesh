#!/usr/bin/env bash
# status.sh — poll the Hetzner fleet for benchmark progress.
#
# Shows:
#   • last 20 lines of the remote log on rm-bench
#   • G2: which result files exist and their sizes
#   • G3: how many problems done (from progress JSONL)
#   • G4: per-problem results (from progress JSONL)
#   • active reasonmesh processes on each node
#
# Usage:
#   source scripts/env.sh
#   ./scripts/status.sh

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
ENV_FILE="$SCRIPT_DIR/env.sh"
[[ -f "$ENV_FILE" ]] || { echo "error: scripts/env.sh not found — run provision.sh first" >&2; exit 1; }
# shellcheck disable=SC1090
source "$ENV_FILE"

GREEN='\033[0;32m'; CYAN='\033[0;36m'; YELLOW='\033[1;33m'; BOLD='\033[1m'; NC='\033[0m'
section() { echo -e "\n${CYAN}── $* ──${NC}"; }
hdr()     { echo -e "${BOLD}$*${NC}"; }

SSH="-i $RM_SSH_KEY -o StrictHostKeyChecking=no -o ConnectTimeout=10 -o ServerAliveInterval=10 -o ServerAliveCountMax=3"
bench() { ssh $SSH "root@$RM_BENCH_IP" "$@" 2>/dev/null; }
node()  { local n=$1; shift; local ip_var="RM_NODE${n}_IP"; ssh $SSH "root@${!ip_var}" "$@" 2>/dev/null; }

RESULTS="/opt/reasonmesh/local/results"
REMOTE_LOG="/tmp/reasonmesh-bench.log"

echo ""
echo -e "${BOLD}ReasonMesh Benchmark Status  $(date +%H:%M:%S)${NC}"
echo    "  bench: $RM_BENCH_IP"

# ── Remote log ────────────────────────────────────────────────────────────────
section "Recent log (rm-bench:$REMOTE_LOG)"
bench "tail -20 $REMOTE_LOG" 2>/dev/null || echo "  (log not found — benchmark not started yet)"

# ── G2 scaling ────────────────────────────────────────────────────────────────
section "G2 scaling results"
G2_OUT=$(bench "ls -la $RESULTS/g2/*.json 2>/dev/null | awk '{print \$5, \$9}'" 2>/dev/null || echo "")
if [[ -z "$G2_OUT" ]]; then
  echo "  No G2 results yet"
else
  G2_DONE=0; G2_EMPTY=0
  while IFS= read -r line; do
    size=$(echo "$line" | awk '{print $1}')
    file=$(echo "$line" | awk '{print $2}' | xargs basename)
    if [[ "$size" -gt 0 ]]; then
      echo -e "  ${GREEN}✓${NC}  $file  (${size}B)"
      G2_DONE=$((G2_DONE + 1))
    else
      echo -e "  ${YELLOW}○${NC}  $file  (empty — re-running)"
      G2_EMPTY=$((G2_EMPTY + 1))
    fi
  done <<< "$G2_OUT"
  echo "  $G2_DONE/9 done, $G2_EMPTY pending"
fi

# ── G3 baselines ──────────────────────────────────────────────────────────────
section "G3 vs baselines"
G3_PROGRESS="$RESULTS/g3/g3-vs-all-baselines.progress.jsonl"
G3_RESULT="$RESULTS/g3/g3-vs-all-baselines.json"
G3_DONE=$(bench "test -f '$G3_PROGRESS' && wc -l < '$G3_PROGRESS' || echo 0" 2>/dev/null || echo 0)
G3_TOTAL=21
if bench "test -f '$G3_RESULT' && grep -q 'outcome' '$G3_RESULT'" 2>/dev/null; then
  echo -e "  ${GREEN}✓  Complete${NC}  ($G3_TOTAL/$G3_TOTAL problems)"
  bench "python3 -c \"import json; d=json.load(open('$G3_RESULT')); s=d['summary']; print(f'  par2={s[\\\"par2_ns\\\"]/1e9:.1f}s  solved={s[\\\"solved\\\"]}/{len(d[\\\"problems\\\"])}')\""  2>/dev/null || true
else
  echo "  In progress: ${G3_DONE}/${G3_TOTAL} problems done"
  if [[ "${G3_DONE:-0}" -gt 0 ]]; then
    echo "  Last completed:"
    bench "tail -3 '$G3_PROGRESS' 2>/dev/null" | \
      python3 -c "import json,sys
for line in sys.stdin:
  try:
    d=json.loads(line)
    print(f'    {d[\"name\"]:30s}  outcome={d[\"outcome\"]}  wall={d[\"wall\"][\"wall_secs\"]:.1f}s')
  except: pass" 2>/dev/null || true
  fi
fi

# ── G4 distributed ────────────────────────────────────────────────────────────
section "G4 distributed"
G4_PROGRESS="$RESULTS/g4/g4-distributed.progress.jsonl"
G4_RESULT="$RESULTS/g4/g4-distributed.json"
if bench "test -f '$G4_RESULT'" 2>/dev/null; then
  echo -e "  ${GREEN}✓  Complete${NC}"
  bench "python3 -c \"
import json
d=json.load(open('$G4_RESULT'))
for p in d['problems']:
  sn=p['single_node']; dist=p['distributed']
  sp=f\\\"{p['speedup']}×\\\" if p['speedup'] else 'timeout'
  print(f\\\"  {p['name']:20s}  sn={sn['verdict'].split()[-1]}({sn['wall_secs']:.0f}s)  dist={dist['verdict'].split()[-1]}({dist['wall_secs']:.0f}s)  speedup={sp}\\\")
\"" 2>/dev/null || bench "cat '$G4_RESULT'" | python3 -c "import json,sys; d=json.load(sys.stdin); [print(f'  {p[\"name\"]:20} sn={p[\"single_node\"][\"verdict\"]} dist={p[\"distributed\"][\"verdict\"]}') for p in d['problems']]" 2>/dev/null || echo "  (could not parse G4 result)"
elif bench "test -s '$G4_PROGRESS'" 2>/dev/null; then
  G4_DONE=$(bench "wc -l < '$G4_PROGRESS'" 2>/dev/null || echo 0)
  echo "  In progress: ${G4_DONE}/5 problems done"
  bench "cat '$G4_PROGRESS' 2>/dev/null" | \
    python3 -c "import json,sys
for line in sys.stdin:
  try:
    p=json.loads(line)
    sn=p['single_node']; dist=p['distributed']
    print(f'  {p[\"name\"]:20s}  sn={sn[\"verdict\"].split()[-1]}({sn[\"wall_secs\"]:.0f}s)  dist={dist[\"verdict\"].split()[-1]}({dist[\"wall_secs\"]:.0f}s)')
  except: pass" 2>/dev/null || true
else
  echo "  Not started yet"
fi

# ── Active processes ──────────────────────────────────────────────────────────
section "Active reasonmesh processes"
for host_label in "rm-bench:$RM_BENCH_IP" "rm-node1:$RM_NODE1_IP" "rm-node2:$RM_NODE2_IP" "rm-node3:$RM_NODE3_IP" "rm-node4:$RM_NODE4_IP"; do
  label="${host_label%%:*}"; ip="${host_label##*:}"
  procs=$(ssh $SSH "root@$ip" "pgrep -a reasonmesh 2>/dev/null | head -3" 2>/dev/null || echo "")
  if [[ -n "$procs" ]]; then
    echo -e "  ${GREEN}●${NC}  $label  $procs"
  else
    echo    "  ○  $label  (idle)"
  fi
done

echo ""

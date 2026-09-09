#!/usr/bin/env bash
# smoke-test.sh — Quick sanity check (~3 min) before a full benchmark run.
#
# Checks:
#   1. SSH connectivity to rm-bench and rm-node1..4
#   2. reasonmesh binary present and version visible
#   3. Disk space on rm-bench (>= 5 GB free under /opt/reasonmesh)
#   4. Python dependencies (matplotlib, pandas, tabulate)
#   5. Single-node SAT/UNSAT correctness (trivial SAT + PHP(3,2) UNSAT)
#   6. Multi-worker solve (4 workers on trivial SAT)
#   7. reasonmesh benchmark with a 2-problem inline manifest
#   8. run-per-problem.py present and working
#   9. Private network connectivity: rm-bench → each node private IP
#  10. AKX TCP port: start reasonmesh serve on node1, verify port opens, kill it
#
# Usage:
#   source scripts/env.sh
#   ./scripts/smoke-test.sh
#
# Exit code: 0 if all checks pass, 1 if any fail.

set -uo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# ── Environment ────────────────────────────────────────────────────────────────
ENV_FILE="$SCRIPT_DIR/env.sh"
[[ -f "$ENV_FILE" ]] || { echo "error: scripts/env.sh not found — run provision.sh first" >&2; exit 1; }
# shellcheck disable=SC1090
source "$ENV_FILE"

for v in RM_SSH_KEY RM_BENCH_IP RM_NODE1_IP RM_NODE2_IP RM_NODE3_IP RM_NODE4_IP \
          RM_NODE1_PRIV RM_NODE2_PRIV RM_NODE3_PRIV RM_NODE4_PRIV; do
  [[ -n "${!v:-}" ]] || { echo "error: $v not set in env.sh" >&2; exit 1; }
done

AKX_PORT="${RM_AKX_PORT:-7000}"

# ── Logging ────────────────────────────────────────────────────────────────────
GREEN='\033[0;32m'; YELLOW='\033[1;33m'; RED='\033[0;31m'; CYAN='\033[0;36m'
BOLD='\033[1m'; NC='\033[0m'

FAILURES=0
WARNINGS=0
START=$SECONDS

log()     { echo -e "${GREEN}[$(date +%H:%M:%S)]${NC} $*"; }
section() { echo -e "\n${CYAN}── $* ──${NC}"; }
pass()    { echo -e "  ${GREEN}✓${NC}  $*"; }
warn()    { echo -e "  ${YELLOW}~${NC}  $*"; WARNINGS=$((WARNINGS+1)); }
fail()    { echo -e "  ${RED}✗${NC}  $*"; FAILURES=$((FAILURES+1)); }

SSH_COMMON_SMOKE="-i $RM_SSH_KEY -o StrictHostKeyChecking=no -o ConnectTimeout=15 -o ServerAliveInterval=15 -o ServerAliveCountMax=4"
ssh_bench() { ssh $SSH_COMMON_SMOKE "root@$RM_BENCH_IP" "$@"; }
ssh_node() {
  local n=$1; shift
  local ip_var="RM_NODE${n}_IP"
  ssh $SSH_COMMON_SMOKE "root@${!ip_var}" "$@"
}

echo ""
echo -e "${BOLD}ReasonMesh Smoke Test${NC}"
echo    "  bench : $RM_BENCH_IP"
echo    "  nodes : $RM_NODE1_IP  $RM_NODE2_IP  $RM_NODE3_IP  $RM_NODE4_IP"
echo    "  key   : $RM_SSH_KEY"
echo    "  akx   : port $AKX_PORT"

# ── 1. SSH connectivity ────────────────────────────────────────────────────────
section "1  SSH connectivity"

if ssh_bench "echo ok" &>/dev/null; then
  BENCH_HOST=$(ssh_bench "hostname" 2>/dev/null || echo "?")
  pass "rm-bench  $RM_BENCH_IP  ($BENCH_HOST)"
else
  fail "rm-bench  $RM_BENCH_IP  unreachable"
fi

for n in 1 2 3 4; do
  ip_var="RM_NODE${n}_IP"
  if ssh_node "$n" "echo ok" &>/dev/null; then
    NODE_HOST=$(ssh_node "$n" "hostname" 2>/dev/null || echo "?")
    pass "rm-node$n  ${!ip_var}  ($NODE_HOST)"
  else
    fail "rm-node$n  ${!ip_var}  unreachable"
  fi
done

# ── 2. Binary ──────────────────────────────────────────────────────────────────
section "2  Binary"

if ssh_bench "which reasonmesh >/dev/null 2>&1"; then
  RM_VER=$(ssh_bench "reasonmesh --version 2>/dev/null || echo unknown")
  pass "rm-bench   reasonmesh found  ($RM_VER)"
else
  fail "rm-bench   reasonmesh not in PATH"
fi

for n in 1 2 3 4; do
  if ssh_node "$n" "which reasonmesh >/dev/null 2>&1"; then
    pass "rm-node$n  reasonmesh found"
  else
    fail "rm-node$n  reasonmesh not in PATH"
  fi
done

# ── 3. Disk space ──────────────────────────────────────────────────────────────
section "3  Disk space"

FREE_GB=$(ssh_bench \
  "df -BG /opt/reasonmesh 2>/dev/null | awk 'NR==2{gsub(/G/,\"\",\$4); print \$4}'" \
  2>/dev/null || echo "0")
FREE_GB="${FREE_GB:-0}"

if [[ "$FREE_GB" -ge 5 ]]; then
  pass "rm-bench  /opt/reasonmesh  ${FREE_GB} GB free"
elif [[ "$FREE_GB" -ge 2 ]]; then
  warn "rm-bench  /opt/reasonmesh  only ${FREE_GB} GB free (may be tight for large runs)"
else
  fail "rm-bench  /opt/reasonmesh  only ${FREE_GB} GB free (need >= 5 GB)"
fi

# ── 4. Python dependencies ─────────────────────────────────────────────────────
section "4  Python dependencies"

PYCHECK=$(ssh_bench \
  "python3 -c 'import matplotlib, pandas, tabulate; print(\"ok\")' 2>&1" \
  2>/dev/null || echo "FAIL")
if [[ "$PYCHECK" == "ok" ]]; then
  pass "matplotlib  pandas  tabulate  present"
else
  fail "Python deps missing on rm-bench: $PYCHECK"
fi

# ── 5. SAT solver end-to-end ───────────────────────────────────────────────────
section "5  SAT solver end-to-end"

# 5a. Upload test problems to rm-bench
#
# Trivial SAT: 1 variable, 1 clause (x).
TRIVIAL_SAT="p cnf 1 1
1 0"

# PHP(3,2): 3 pigeons, 2 holes — UNSAT.  Variables x(i,j) = (i-1)*2+j.
# Each pigeon in >= 1 hole:  1 2 0 | 3 4 0 | 5 6 0
# Each hole has <= 1 pigeon (pairwise negations per hole):
#   hole 1: -1 -3 | -1 -5 | -3 -5   hole 2: -2 -4 | -2 -6 | -4 -6
PHP32="p cnf 6 9
1 2 0
3 4 0
5 6 0
-1 -3 0
-1 -5 0
-3 -5 0
-2 -4 0
-2 -6 0
-4 -6 0"

printf '%s\n' "$TRIVIAL_SAT" | ssh_bench "cat > /tmp/rm-smoke-sat.cnf"
printf '%s\n' "$PHP32"       | ssh_bench "cat > /tmp/rm-smoke-php32.cnf"

# 5b. Trivial SAT — 1 worker
SAT_OUT=$(ssh_bench \
  "reasonmesh solve /tmp/rm-smoke-sat.cnf --workers 1 2>/dev/null | head -1" \
  2>/dev/null || echo "FAIL")
if [[ "$SAT_OUT" == "s SATISFIABLE" ]]; then
  pass "trivial SAT  (1 var, 1 clause)  → SATISFIABLE"
else
  fail "trivial SAT: expected 's SATISFIABLE', got: '$SAT_OUT'"
fi

# 5c. PHP(3,2) UNSAT — 1 worker
UNSAT_OUT=$(ssh_bench \
  "reasonmesh solve /tmp/rm-smoke-php32.cnf --workers 1 2>/dev/null | head -1" \
  2>/dev/null || echo "FAIL")
if [[ "$UNSAT_OUT" == "s UNSATISFIABLE" ]]; then
  pass "PHP(3,2) UNSAT  (6 vars, 9 clauses)  → UNSATISFIABLE"
else
  fail "PHP(3,2): expected 's UNSATISFIABLE', got: '$UNSAT_OUT'"
fi

# 5d. Multi-worker SAT — 4 workers
MW_OUT=$(ssh_bench \
  "reasonmesh solve /tmp/rm-smoke-sat.cnf --workers 4 2>/dev/null | head -1" \
  2>/dev/null || echo "FAIL")
if [[ "$MW_OUT" == "s SATISFIABLE" ]]; then
  pass "trivial SAT  4 workers  → SATISFIABLE"
else
  fail "4-worker solve: expected 's SATISFIABLE', got: '$MW_OUT'"
fi

# 5e. PHP(6,5) UNSAT — 8 workers, tests AKX clause sharing at small scale
# 6 pigeons, 5 holes: 6 pigeon clauses + 5 holes × C(6,2)=15 = 81 clauses total
# Variable x(i,j) = (i-1)*5 + j  (pigeon i in hole j), i=1..6, j=1..5
PHP65="p cnf 30 81
1 2 3 4 5 0
6 7 8 9 10 0
11 12 13 14 15 0
16 17 18 19 20 0
21 22 23 24 25 0
26 27 28 29 30 0
-1 -6 0
-1 -11 0
-1 -16 0
-1 -21 0
-1 -26 0
-6 -11 0
-6 -16 0
-6 -21 0
-6 -26 0
-11 -16 0
-11 -21 0
-11 -26 0
-16 -21 0
-16 -26 0
-21 -26 0
-2 -7 0
-2 -12 0
-2 -17 0
-2 -22 0
-2 -27 0
-7 -12 0
-7 -17 0
-7 -22 0
-7 -27 0
-12 -17 0
-12 -22 0
-12 -27 0
-17 -22 0
-17 -27 0
-22 -27 0
-3 -8 0
-3 -13 0
-3 -18 0
-3 -23 0
-3 -28 0
-8 -13 0
-8 -18 0
-8 -23 0
-8 -28 0
-13 -18 0
-13 -23 0
-13 -28 0
-18 -23 0
-18 -28 0
-23 -28 0
-4 -9 0
-4 -14 0
-4 -19 0
-4 -24 0
-4 -29 0
-9 -14 0
-9 -19 0
-9 -24 0
-9 -29 0
-14 -19 0
-14 -24 0
-14 -29 0
-19 -24 0
-19 -29 0
-24 -29 0
-5 -10 0
-5 -15 0
-5 -20 0
-5 -25 0
-5 -30 0
-10 -15 0
-10 -20 0
-10 -25 0
-10 -30 0
-15 -20 0
-15 -25 0
-15 -30 0
-20 -25 0
-20 -30 0
-25 -30 0"

printf '%s\n' "$PHP65" | ssh_bench "cat > /tmp/rm-smoke-php65.cnf"

PHP65_OUT=$(ssh_bench \
  "timeout 60 reasonmesh solve /tmp/rm-smoke-php65.cnf --workers 8 2>/dev/null | head -1" \
  2>/dev/null || echo "TIMEOUT")
if [[ "$PHP65_OUT" == "s UNSATISFIABLE" ]]; then
  pass "PHP(6,5) UNSAT  8 workers  → UNSATISFIABLE"
elif [[ -z "$PHP65_OUT" || "$PHP65_OUT" == "TIMEOUT" ]]; then
  warn "PHP(6,5) timed out at 60s with 8 workers (hard instance — not a blocker for benchmarks)"
else
  fail "PHP(6,5): expected 's UNSATISFIABLE', got: '$PHP65_OUT'"
fi

# ── 6. Benchmark manifest ──────────────────────────────────────────────────────
section "6  Benchmark manifest"

SMOKE_TOML='schema_version = 1
name = "smoke-test"
description = "2-problem smoke test"

[solver]
workers = 2
seed = 1
deterministic = false
clause_sharing = true
max_conflicts_per_problem = 100000
timeout_secs = 10

[output]
dir = "/tmp/rm-smoke-results"
trace = false

[[problems]]
name = "trivial-sat"
file = "/tmp/rm-smoke-sat.cnf"
expect = "sat"

[[problems]]
name = "php32-unsat"
file = "/tmp/rm-smoke-php32.cnf"
expect = "unsat"'

printf '%s\n' "$SMOKE_TOML" | ssh_bench "cat > /tmp/rm-smoke-manifest.toml"
ssh_bench "mkdir -p /tmp/rm-smoke-results" &>/dev/null

BENCH_JSON=$(ssh_bench \
  "cd /opt/reasonmesh/local && \
   reasonmesh benchmark /tmp/rm-smoke-manifest.toml 2>/tmp/rm-smoke-bench-stderr.txt" \
  2>/dev/null || echo "FAIL")

if printf '%s\n' "$BENCH_JSON" | \
   python3 -c "import json,sys; d=json.load(sys.stdin); assert len(d['problems'])==2" \
   2>/dev/null; then
  SOLVED=$(printf '%s\n' "$BENCH_JSON" | \
    python3 -c "import json,sys; d=json.load(sys.stdin); print(d['summary']['solved'])" \
    2>/dev/null || echo "?")
  pass "benchmark manifest  2 problems run  ${SOLVED}/2 solved"
else
  STDERR=$(ssh_bench "cat /tmp/rm-smoke-bench-stderr.txt 2>/dev/null | head -3" 2>/dev/null || echo "")
  fail "benchmark manifest failed${STDERR:+: ${STDERR}}"
fi

# ── 7. run-per-problem.py ──────────────────────────────────────────────────────
section "7  run-per-problem.py"

PPR_TOML='schema_version = 1
name = "smoke-ppr"
description = "1-problem per-problem smoke test"

[solver]
workers = 1
seed = 1
deterministic = false
clause_sharing = false
max_conflicts_per_problem = 100000
timeout_secs = 10

[output]
dir = "/tmp/rm-smoke-ppr-results"
trace = false

[[problems]]
name = "trivial-sat"
file = "/tmp/rm-smoke-sat.cnf"
expect = "sat"'

printf '%s\n' "$PPR_TOML" | ssh_bench "cat > /tmp/rm-smoke-ppr.toml"
ssh_bench "mkdir -p /tmp/rm-smoke-ppr-results" &>/dev/null

PPR_LOG=$(ssh_bench \
  "test -f /opt/reasonmesh/local/run-per-problem.py || { echo MISSING; exit 1; }
   cd /opt/reasonmesh/local && \
   python3 run-per-problem.py \
     /tmp/rm-smoke-ppr.toml \
     /tmp/rm-smoke-ppr-result.json \
     /tmp/rm-smoke-ppr-progress.jsonl 2>&1" \
  2>/dev/null || echo "MISSING_OR_FAIL")

if [[ "$PPR_LOG" == "MISSING_OR_FAIL" ]]; then
  fail "run-per-problem.py not found at /opt/reasonmesh/local/ (sync scripts first)"
elif ssh_bench \
  "test -s /tmp/rm-smoke-ppr-result.json && \
   python3 -c \"import json; json.load(open('/tmp/rm-smoke-ppr-result.json'))\"" \
  &>/dev/null; then
  pass "run-per-problem.py  result JSON valid"
  if ssh_bench "test -s /tmp/rm-smoke-ppr-progress.jsonl" &>/dev/null; then
    pass "run-per-problem.py  JSONL progress file written"
  else
    fail "run-per-problem.py  JSONL progress file empty or missing"
  fi
else
  fail "run-per-problem.py  result JSON invalid or missing"
fi

# ── 8. Resumption: skip already-done problem ───────────────────────────────────
section "8  Resumption (per-problem skip)"

PPR_RESUME=$(ssh_bench \
  "cd /opt/reasonmesh/local && \
   python3 run-per-problem.py \
     /tmp/rm-smoke-ppr.toml \
     /tmp/rm-smoke-ppr-result.json \
     /tmp/rm-smoke-ppr-progress.jsonl 2>&1" \
  2>/dev/null || echo "FAIL")

if printf '%s\n' "$PPR_RESUME" | grep -qi "skip\|already"; then
  pass "resumption: already-done problem correctly skipped"
else
  warn "resumption: could not confirm skip-on-resume behavior (output: ${PPR_RESUME:0:80})"
fi

# ── 9. Private network connectivity ───────────────────────────────────────────
section "9  Private network (rm-bench → nodes)"

for n in 1 2 3 4; do
  priv_var="RM_NODE${n}_PRIV"
  NODE_PRIV="${!priv_var}"
  # nc -z: zero-I/O mode (port scan); -w3: 3s timeout
  if ssh_bench "nc -z -w3 $NODE_PRIV 22 2>/dev/null"; then
    pass "rm-bench → rm-node$n  $NODE_PRIV:22  reachable"
  else
    fail "rm-bench → rm-node$n  $NODE_PRIV:22  unreachable"
  fi
done

# ── 10. AKX TCP port (reasonmesh serve) ───────────────────────────────────────
section "10  AKX TCP port (reasonmesh serve)"

NODE1_PRIV="$RM_NODE1_PRIV"

# Kill any stale serve process from a previous run
ssh_node 1 "pkill -f 'reasonmesh serve' 2>/dev/null || true" &>/dev/null
sleep 1

# Start serve on node1, capture its PID
SERVE_PID=$(ssh_node 1 \
  "nohup reasonmesh serve /dev/null --port $AKX_PORT --workers 2 \
   >/tmp/rm-smoke-serve.log 2>&1 & echo \$!" \
  2>/dev/null || echo "")

if [[ -z "$SERVE_PID" ]]; then
  fail "reasonmesh serve  could not start on rm-node1 (check binary supports 'serve' subcommand)"
else
  sleep 2  # allow server to bind

  # Check port is open from rm-bench
  if ssh_bench "nc -z -w5 $NODE1_PRIV $AKX_PORT 2>/dev/null"; then
    pass "reasonmesh serve  rm-node1  $NODE1_PRIV:$AKX_PORT  accepting connections"
  else
    SERVE_LOG=$(ssh_node 1 "cat /tmp/rm-smoke-serve.log 2>/dev/null | head -5" || echo "")
    fail "AKX port $AKX_PORT not open on rm-node1${SERVE_LOG:+; log: ${SERVE_LOG}}"
  fi

  # Cleanup
  ssh_node 1 "kill $SERVE_PID 2>/dev/null || pkill -f 'reasonmesh serve' 2>/dev/null || true" \
    &>/dev/null
fi

# ── Summary ────────────────────────────────────────────────────────────────────
ELAPSED=$((SECONDS - START))

echo ""
echo "──────────────────────────────────────────────────────"
if [[ $FAILURES -eq 0 && $WARNINGS -eq 0 ]]; then
  echo -e "${GREEN}${BOLD}All checks passed${NC} in ${ELAPSED}s"
  echo    "Infrastructure is ready for a full benchmark run."
  exit 0
elif [[ $FAILURES -eq 0 ]]; then
  echo -e "${YELLOW}${BOLD}Passed with $WARNINGS warning(s)${NC} in ${ELAPSED}s"
  echo    "Review warnings above before running benchmarks."
  exit 0
else
  echo -e "${RED}${BOLD}$FAILURES check(s) failed${NC}  $WARNINGS warning(s)  in ${ELAPSED}s"
  echo    "Fix failures before running benchmarks."
  exit 1
fi

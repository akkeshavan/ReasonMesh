#!/usr/bin/env bash
# Run a benchmark manifest in the background, detached from the terminal.
# Usage: scripts/bench-bg.sh experiments/<manifest>.toml [output-stem]
#
# Output goes to:
#   <output-stem>.json      — full JSON result (written atomically on completion)
#   <output-stem>.ckpt      — NDJSON checkpoint (one result per line, flushed live)
#   <output-stem>.log       — stderr (progress info, solver eprintlns)
#
# Checkpointing: each problem result is appended to .ckpt immediately when it
# finishes. If the run is killed and restarted with the same output-stem, the
# solver skips already-completed problems and resumes from where it left off.
#
# The script prints the PID so you can tail the log or kill the run.
# Builds the binary first if it is stale.

set -euo pipefail

MANIFEST="${1:?Usage: bench-bg.sh <manifest.toml> [output-stem]}"
STEM="${2:-bench-$(basename "${MANIFEST%.toml}")}"

JSON="${STEM}.json"
CKPT="${STEM}.ckpt"
LOG="${STEM}.log"

# Build release binary before detaching so build errors surface immediately.
echo "Building release binary..."
cargo build --release -p reasonmesh-cli 2>&1

BINARY="$(cargo metadata --format-version 1 --no-deps 2>/dev/null \
  | python3 -c "import sys,json; d=json.load(sys.stdin); print(d['target_directory'])")/release/reasonmesh"

if [[ ! -x "$BINARY" ]]; then
  echo "error: binary not found at $BINARY" >&2
  exit 1
fi

if [[ -f "$CKPT" ]]; then
  N=$(wc -l < "$CKPT" | tr -d ' ')
  echo "Resuming from checkpoint: $N problems already done ($CKPT)"
fi

# Detach: nohup + setsid prevents SIGHUP from a closed terminal.
# nice -n 10 keeps the run below interactive work.
# ulimit -v 8000000 caps virtual memory at ~8 GB per process to prevent OOM.
nohup nice -n 10 bash -c "
  ulimit -v 8000000 2>/dev/null || true
  exec '$BINARY' benchmark --checkpoint '$CKPT' '$MANIFEST'
" > "$JSON" 2> "$LOG" &

PID=$!
echo "Benchmark running in background (PID $PID)"
echo "  results    → $JSON   (written on completion)"
echo "  checkpoint → $CKPT   (live, flushed per problem)"
echo "  log        → $LOG"
echo ""
echo "Monitor:  tail -f $LOG"
echo "Resume:   bash scripts/bench-bg.sh $MANIFEST $STEM   (re-uses checkpoint)"
echo "Kill:     kill $PID"

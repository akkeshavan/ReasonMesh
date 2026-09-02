#!/usr/bin/env bash
# Run TLC on both model configurations.
# Requires: TLA+ Toolbox tools on PATH, or set TLCJAR to the path of tla2tools.jar.
#
# Install (macOS):
#   brew install tla-tools          # if available, or
#   wget https://github.com/tlaplus/tlaplus/releases/latest/download/tla2tools.jar
#
# Usage:
#   cd tla && bash check.sh
#   cd tla && bash check.sh safety    # safety only (fast, seconds)
#   cd tla && bash check.sh liveness  # safety + strong liveness (slower)

set -euo pipefail
cd "$(dirname "$0")"

TLCJAR="${TLCJAR:-tla2tools.jar}"
JAVA="${JAVA:-java}"
TLC_FLAGS="-workers auto -cleanup"

if ! command -v tlc &>/dev/null && [[ ! -f "$TLCJAR" ]]; then
    echo "Error: tlc not on PATH and $TLCJAR not found."
    echo "Download from: https://github.com/tlaplus/tlaplus/releases"
    exit 1
fi

run_tlc() {
    local module="$1" cfg="$2" label="$3"
    echo ""
    echo "================================================================"
    echo "  $label"
    echo "  Module: $module.tla   Config: $cfg"
    echo "================================================================"
    if command -v tlc &>/dev/null; then
        tlc "$module" -config "$cfg" $TLC_FLAGS
    else
        "$JAVA" -jar "$TLCJAR" "$module" -config "$cfg" $TLC_FLAGS
    fi
}

MODE="${1:-all}"

case "$MODE" in
    safety)
        run_tlc MC MC.cfg \
            "Safety check: I1-I5 + weak liveness L1-L4 (Timeout enabled)"
        ;;
    liveness)
        run_tlc MC_NoTimeout MC_NoTimeout.cfg \
            "Strong liveness: L5-L7 (Timeout excluded)"
        ;;
    all|*)
        run_tlc MC MC.cfg \
            "Safety check: I1-I5 + weak liveness L1-L4 (Timeout enabled)"
        run_tlc MC_NoTimeout MC_NoTimeout.cfg \
            "Strong liveness: L5-L7 (Timeout excluded)"
        echo ""
        echo "All checks passed."
        ;;
esac

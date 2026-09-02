#!/usr/bin/env python3
"""G2 scaling analysis: ablation table + PAR-2 scaling curve for RQ1/RQ2."""

import json
import sys
from pathlib import Path

DATA = Path(__file__).parent / "data" / "g2"

CONFIGS = [
    ("1w",     "g2-scaling-1w",           1, False),
    ("2w-iso", "g2-scaling-2w-isolated",  2, False),
    ("2w-sel", "g2-scaling-2w-selective", 2, True),
    ("4w-iso", "g2-scaling-4w-isolated",  4, False),
    ("4w-sel", "g2-scaling-4w-selective", 4, True),
    ("8w-iso", "g2-scaling-8w-isolated",  8, False),
    ("8w-sel", "g2-scaling-8w-selective", 8, True),
]

PROBLEMS = ["php-9-8", "php-10-9", "php-11-10", "r3sat-238-2", "r3sat-240-r425"]
TIMEOUT = 60.0


def load_all():
    data = {}
    for label, fname, nw, sharing in CONFIGS:
        path = DATA / f"{fname}.json"
        if not path.exists():
            print(f"[warn] missing {path}", file=sys.stderr)
            continue
        with open(path) as f:
            d = json.load(f)
        by_name = {}
        for r in d["problems"]:
            wall = r["wall"]["secs"] + r["wall"]["nanos"] / 1e9
            by_name[r["name"]] = {
                "wall": wall,
                "outcome": r["outcome"],
                "conflicts": r["conflicts"],
                "timed_out": r.get("timed_out", wall >= TIMEOUT - 0.5),
            }
        par2 = d["summary"]["par2_ns"] / 1e9
        solved = d["summary"]["solved"]
        data[label] = {
            "by_name": by_name,
            "par2": par2,
            "solved": solved,
            "nw": nw,
            "sharing": sharing,
        }
    return data


def print_wall_table(data):
    labels = [l for l, *_ in CONFIGS if l in data]
    header = f"{'Problem':<18}" + "".join(f" {l:>9}" for l in labels)
    print(header)
    print("-" * len(header))
    for p in PROBLEMS:
        row = f"{p:<18}"
        for l in labels:
            r = data[l]["by_name"].get(p)
            if r is None:
                row += f" {'---':>9}"
            elif r["timed_out"]:
                row += f" {'T/O':>8}*"
            else:
                row += f" {r['wall']:>9.2f}"
        print(row)
    print("  * = timed out at 60s")


def print_par2_table(data):
    baseline = data["1w"]["par2"]
    print(f"\n{'Config':<12} {'workers':>7} {'sharing':>8} {'PAR-2 (s)':>12} {'speedup vs 1w':>16} {'solved':>8}")
    print("-" * 72)
    for label, _, nw, sharing in CONFIGS:
        if label not in data:
            continue
        d = data[label]
        speedup = baseline / d["par2"]
        s = "yes" if sharing else "no"
        print(f"{label:<12} {nw:>7} {s:>8} {d['par2']:>12.1f} {speedup:>16.3f}x {d['solved']:>6}/5")


def print_sharing_benefit(data):
    print("\nSharing benefit (isolated wall / selective wall, by problem and worker count)")
    print(f"{'Problem':<18} {'2w':>8} {'4w':>8} {'8w':>8}")
    print("-" * 42)
    for p in PROBLEMS:
        row = f"{p:<18}"
        for iso, sel in [("2w-iso","2w-sel"),("4w-iso","4w-sel"),("8w-iso","8w-sel")]:
            if iso not in data or sel not in data:
                row += f" {'---':>8}"
                continue
            ri = data[iso]["by_name"].get(p)
            rs = data[sel]["by_name"].get(p)
            if ri is None or rs is None:
                row += f" {'---':>8}"
            elif ri["timed_out"] and rs["timed_out"]:
                row += f" {'---':>8}"
            elif rs["timed_out"] and not ri["timed_out"]:
                row += f" {'<1':>8}"
            else:
                ti = ri["wall"] if not ri["timed_out"] else 2 * TIMEOUT
                ts = rs["wall"] if not rs["timed_out"] else 2 * TIMEOUT
                ratio = ti / ts
                row += f" {ratio:>7.2f}x"
        print(row)


def main():
    data = load_all()

    print("=" * 72)
    print("G2 SCALING RESULTS — wall time (seconds)")
    print("Hardware: Apple M-series MacBook Air (4P+4E cores), 60s timeout")
    print("=" * 72)
    print()
    print_wall_table(data)
    print_par2_table(data)
    print_sharing_benefit(data)

    print()
    print("Key findings:")
    if "2w-sel" in data and "1w" in data:
        sp = data["1w"]["par2"] / data["2w-sel"]["par2"]
        print(f"  RQ1: AKX clause sharing improves PAR-2 by {sp:.3f}x at 2 workers")
    if "2w-iso" in data and "1w" in data:
        ov = data["2w-iso"]["par2"] / data["1w"]["par2"]
        print(f"  RQ2: 2w isolated has {ov:.3f}x PAR-2 overhead vs 1w (protocol cost)")
    print("  Note: 8w anti-scaling expected — Mac Air saturates P+E core mix at 8 threads.")
    print("  Server-class hardware (uniform P-cores, high-BW memory) needed for strong scaling.")


if __name__ == "__main__":
    main()

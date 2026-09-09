#!/usr/bin/env python3
"""
Run a reasonmesh benchmark manifest one problem at a time, writing a JSONL
progress line after each problem finishes.

Usage:
    python3 run-per-problem.py <manifest.toml> <result.json> <progress.jsonl>

Replaces a single reasonmesh benchmark <manifest> call for large manifests
(e.g. G3) where you need to track progress mid-run.
"""

import sys
import os
import json
import time
import subprocess
import tempfile

try:
    import tomllib
except ImportError:
    sys.exit("Python 3.11+ required (tomllib); found " + sys.version.split()[0])


def strip_problems(content: str) -> str:
    """Remove every [[problems]] block from raw TOML text."""
    out, skip = [], False
    for line in content.splitlines(keepends=True):
        s = line.strip()
        if s == "[[problems]]":
            skip = True
        elif s.startswith("[[") and s.endswith("]]"):
            skip = False
        if not skip:
            out.append(line)
    return "".join(out)


def write_single_problem_manifest(base: str, prob: dict, manifest_dir: str) -> str:
    lines = ["\n[[problems]]"]
    for k, v in prob.items():
        # Resolve relative file paths to absolute so the temp manifest in /tmp works
        # regardless of where reasonmesh resolves paths from.
        if k == "file" and isinstance(v, str) and not os.path.isabs(v):
            v = os.path.normpath(os.path.join(manifest_dir, v))
        if isinstance(v, str):
            lines.append(f'{k} = "{v}"')
        elif isinstance(v, bool):
            lines.append(f'{k} = {"true" if v else "false"}')
        else:
            lines.append(f"{k} = {json.dumps(v)}")
    fd, path = tempfile.mkstemp(suffix=".toml", prefix="rm-pp-", dir="/tmp")
    with os.fdopen(fd, "w") as f:
        f.write(base + "\n".join(lines) + "\n")
    return path


def main():
    if len(sys.argv) != 4:
        sys.exit(f"Usage: {sys.argv[0]} <manifest.toml> <result.json> <progress.jsonl>")

    manifest_path, result_path, progress_path = sys.argv[1], sys.argv[2], sys.argv[3]
    manifest_dir = os.path.dirname(os.path.abspath(manifest_path))

    with open(manifest_path) as f:
        raw = f.read()
    with open(manifest_path, "rb") as f:
        m = tomllib.load(f)

    problems = m.get("problems", [])
    timeout = m.get("solver", {}).get("timeout_secs", 300)
    n = len(problems)
    base = strip_problems(raw)

    # Load already-completed problems from an existing progress JSONL (resumption).
    done_names: set = set()
    done_results: dict = {}
    if os.path.exists(progress_path):
        with open(progress_path) as pf:
            for line in pf:
                line = line.strip()
                if not line:
                    continue
                try:
                    entry = json.loads(line)
                    pname = entry.get("problem")
                    if pname:
                        done_names.add(pname)
                        done_results[pname] = entry
                except json.JSONDecodeError:
                    pass
    if done_names:
        print(f"Resuming: {len(done_names)} problems already done: {sorted(done_names)}", flush=True)

    all_results = []
    run_start = time.time()

    for i, prob in enumerate(problems, start=1):
        name = prob["name"]

        if name in done_names:
            print(f"[{i}/{n}] SKIP {name} (already in progress file)", flush=True)
            # Reconstruct the prob_data from the saved progress entry if possible.
            saved = done_results[name]
            all_results.append(saved.get("prob_data") or {"name": name})
            continue

        print(f"[{i}/{n}] {name} ...", flush=True)

        tmp = write_single_problem_manifest(base, prob, manifest_dir)
        t0 = time.time()
        try:
            r = subprocess.run(
                ["reasonmesh", "benchmark", tmp],
                capture_output=True,
                text=True,
                timeout=timeout * 5 + 60,  # 4 solvers + headroom
            )
            if r.returncode == 0 and r.stdout.strip():
                bench = json.loads(r.stdout)
                prob_data = (bench.get("problems") or [{"name": name}])[0]
            else:
                prob_data = {"name": name, "error": (r.stderr or f"exit {r.returncode}")[:300]}
        except subprocess.TimeoutExpired:
            prob_data = {"name": name, "error": "runner timeout"}
        except Exception as e:
            prob_data = {"name": name, "error": str(e)}
        finally:
            os.unlink(tmp)

        wall = round(time.time() - t0, 3)
        all_results.append(prob_data)
        outcome = prob_data.get("outcome", "?")

        with open(progress_path, "a") as pf:
            pf.write(json.dumps({"idx": i, "n": n, "problem": name,
                                 "wall_secs": wall, "outcome": outcome,
                                 "prob_data": prob_data}) + "\n")

        print(f"[{i}/{n}] DONE {name}: {outcome} in {wall:.1f}s", flush=True)

    total = round(time.time() - run_start, 3)
    final = {
        "schema_version": 1,
        "experiment": m.get("name", ""),
        "description": m.get("description", ""),
        "problems": all_results,
        "summary": {"total_wall_secs": total, "n_problems": n},
    }
    with open(result_path, "w") as f:
        json.dump(final, f, indent=2)

    print(f"ALL DONE — {n} problems in {total:.1f}s", flush=True)


if __name__ == "__main__":
    main()

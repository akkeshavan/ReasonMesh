#!/usr/bin/env python3
"""Sample SMT-LIB benchmarks and generate a bench experiment TOML."""

import os, random, re, sys, argparse

def get_status(path):
    """Extract :status from the first 30 lines of an SMT2 file."""
    try:
        with open(path, 'r', errors='replace') as f:
            for i, line in enumerate(f):
                if i > 30:
                    break
                m = re.search(r':status\s+(sat|unsat|unknown)', line)
                if m:
                    return m.group(1)
    except Exception:
        pass
    return None

def collect(root, logic, n, seed=42):
    """Randomly sample n smt2 files with known sat/unsat status."""
    rng = random.Random(seed)
    all_files = []
    for dirpath, _, filenames in os.walk(root):
        for fn in filenames:
            if fn.endswith('.smt2'):
                all_files.append(os.path.join(dirpath, fn))
    rng.shuffle(all_files)
    results = []
    for path in all_files:
        if len(results) >= n:
            break
        status = get_status(path)
        if status in ('sat', 'unsat'):
            rel = os.path.relpath(path, start='.')
            name = logic + '/' + os.path.relpath(path, root).replace(os.sep, '/')
            results.append((name, rel, status))
    return results

def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--n', type=int, default=200, help='samples per logic')
    parser.add_argument('--out', default='experiments/smtlib-real.toml')
    parser.add_argument('--timeout', type=int, default=30)
    args = parser.parse_args()

    base = 'benchmarks/smtlib/non-incremental'
    logics = [
        ('QF_UF',    os.path.join(base, 'QF_UF')),
        ('QF_UFIDL', os.path.join(base, 'QF_UFIDL')),
        ('QF_UFLIA', os.path.join(base, 'QF_UFLIA')),
    ]

    all_problems = []
    for logic, root in logics:
        problems = collect(root, logic, args.n)
        print(f'{logic}: sampled {len(problems)} problems', file=sys.stderr)
        all_problems.extend(problems)

    lines = [
        'schema_version = 1',
        'name = "smtlib-real"',
        f'description = "SMT-LIB 2025 benchmarks: {len(all_problems)} problems across QF_UF, QF_UFIDL, QF_UFLIA. rm-sat vs Z3."',
        '',
        '[solver]',
        f'timeout_secs = {args.timeout}',
        'parallel_problems = 4',
        '',
        '[[baselines]]',
        'name = "z3"',
        'binary = "z3"',
        'args   = []',
        'workers = 1',
        '',
    ]
    for name, path, status in all_problems:
        lines += [
            '[[problems]]',
            f'name = "{name}"',
            f'file = "../{path}"',
            f'expect = "{status}"',
            '',
        ]

    os.makedirs(os.path.dirname(args.out), exist_ok=True)
    with open(args.out, 'w') as f:
        f.write('\n'.join(lines))
    print(f'Wrote {args.out} with {len(all_problems)} problems', file=sys.stderr)

if __name__ == '__main__':
    main()

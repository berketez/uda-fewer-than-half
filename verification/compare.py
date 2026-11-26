#!/usr/bin/env python3
"""compare.py -- compare the outputs of ./run_all.sh (out/) with the reference outputs (expected/).

Usage: python3 compare.py [--strict] [--allow-missing] [--out out] [--expected expected]
  --allow-missing  report reference files without a counterpart in out/ as NOT RUN instead of failing
                   (use it after ./run_all.sh --quick)

Every file under expected/ must exist under out/. Text files are compared line by line after wall-clock
times of the form "[12.3 s]" have been masked; all other text, every verdict and every number must agree.
Other files (the generated corrupted certificates, *.json) must be byte-identical.
out/run_log.tsv is checked for the exit code of every run (several negative checks must exit with 1);
its wall-clock column is ignored, as are environment.txt, resources.tsv and the out/time/ directory.

Two kinds of difference are reported but tolerated unless --strict is given:
  HINT   numbers that depend on the floating-point Cholesky HINT of the exact verifiers (the residual norm ||E||,
         the ratio printed next to it, the certified lower bounds lambda_min >= ..., sigma >= ..., tau'/w^dag w,
         and quantities computed from them). A different BLAS/LAPACK build can produce a slightly different hint;
         the verdict then still has to be the same, but these certified bounds may differ in the last digits.
  FLOAT  floating-point display values in the scripts that are not exact verifiers (thresholds/thm1_constants.py,
         thresholds/lagrangian_cover.py part (i), numerics/direct_glue_rank.py), compared with relative tolerance 1e-6.
Any other difference is a MISMATCH. Exit status: 0 if there is no MISMATCH (and, with --strict, no HINT/FLOAT
difference either), 1 otherwise. On the machine that produced expected/ the comparison is expected to be exact.
"""
import argparse
import csv
import os
import re
import sys

TIME_RE = re.compile(r"\[\s*[0-9]+(?:\.[0-9]+)?\s*s\]")
NUM = r"[-+]?(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)(?:[eE][-+]?[0-9]+)?"
NUM_RE = re.compile(NUM)
# label -> a number that depends on the Cholesky hint
HINT_PATTERNS = [re.compile(p) for p in (
    r"(‖E‖_∞ ?= ?)" + NUM, r"(‖E‖≤)" + NUM, r"(\(ratio )" + NUM,
    r"(λ_min\([^)]*\) ≥ )" + NUM, r"(λ_min ≥ )" + NUM,
    r"(σ_min\(B_ŵ\)² ≥ )" + NUM, r"(σ_min\(B_ψ₀\) ≥ )" + NUM,
    r"(σ_D\(B\^C_ψ₀\) ≥ )" + NUM, r"(σ_2D\(B_ψ₀\) ≥ )" + NUM,
    r"(τ'/w†w = )" + NUM, r"(rhs = )" + NUM, r"(A ⪰ )" + NUM, r"(G ⪰ )" + NUM,
    r"(D4: 2\(M\+2\) r̂²/\(θ−s\)² = " + NUM + r" < )" + NUM,
)]
FLOAT_FILES = {"thm1_constants.txt", "lagrangian_cover.txt", "numerics_glue_8x4_K3_K4.txt"}
IGNORED = {"environment.txt", "run_log.tsv", "resources.tsv"}


def norm_time(s):
    return TIME_RE.sub("[<time> s]", s)


def mask_hint(s):
    for p in HINT_PATTERNS:
        s = p.sub(lambda m: m.group(1) + "<hint>", s)
    return s


def float_close(a, b, rel=1e-6):
    ta, tb = NUM_RE.findall(a), NUM_RE.findall(b)
    if NUM_RE.sub("#", a) != NUM_RE.sub("#", b) or len(ta) != len(tb):
        return False
    for x, y in zip(ta, tb):
        if x == y:
            continue
        if re.fullmatch(r"[-+]?[0-9]+", x) and re.fullmatch(r"[-+]?[0-9]+", y):
            return False
        fx, fy = float(x), float(y)
        if abs(fx - fy) > rel * max(abs(fx), abs(fy), 1e-300):
            return False
    return True


def compare_text(name, pe, po):
    le = [norm_time(l.rstrip("\n")) for l in open(pe, encoding="utf-8")]
    lo = [norm_time(l.rstrip("\n")) for l in open(po, encoding="utf-8")]
    res = {"MATCH": 0, "HINT": 0, "FLOAT": 0, "MISMATCH": 0}
    notes = []
    if len(le) != len(lo):
        res["MISMATCH"] += 1
        notes.append(f"    number of lines differs: expected {len(le)}, out {len(lo)}")
    for i, (a, b) in enumerate(zip(le, lo), 1):
        if a == b:
            res["MATCH"] += 1
        elif mask_hint(a) == mask_hint(b):
            res["HINT"] += 1
            notes.append(f"    line {i} HINT\n      expected: {a}\n      out:      {b}")
        elif os.path.basename(name) in FLOAT_FILES and float_close(a, b):
            res["FLOAT"] += 1
            notes.append(f"    line {i} FLOAT\n      expected: {a}\n      out:      {b}")
        else:
            res["MISMATCH"] += 1
            notes.append(f"    line {i} MISMATCH\n      expected: {a}\n      out:      {b}")
    return res, notes


def read_log(p):
    with open(p, encoding="utf-8") as fh:
        return {r["name"]: r["exit_code"] for r in csv.DictReader(fh, delimiter="\t")}


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--strict", action="store_true")
    ap.add_argument("--allow-missing", action="store_true")
    ap.add_argument("--out", default="out")
    ap.add_argument("--expected", default="expected")
    a = ap.parse_args()
    os.chdir(os.path.dirname(os.path.abspath(__file__)))
    bad_files, warn_files, not_run, n_files = [], [], [], 0
    for root, _, files in os.walk(a.expected):
        for fn in sorted(files):
            pe = os.path.join(root, fn)
            rel = os.path.relpath(pe, a.expected)
            if rel in IGNORED:
                continue
            po = os.path.join(a.out, rel)
            n_files += 1
            if not os.path.exists(po):
                if a.allow_missing:
                    print(f"NOT RUN   {rel}")
                    not_run.append(rel)
                else:
                    print(f"MISSING  {rel}")
                    bad_files.append(rel)
                continue
            if fn.endswith(".txt"):
                res, notes = compare_text(rel, pe, po)
                status = "MISMATCH" if res["MISMATCH"] else ("TOLERATED" if res["HINT"] or res["FLOAT"] else "IDENTICAL")
                print(f"{status:9s} {rel}  (lines: {res['MATCH']} identical, {res['HINT']} HINT, {res['FLOAT']} FLOAT, "
                      f"{res['MISMATCH']} MISMATCH)")
                for nline in notes:
                    print(nline)
                if res["MISMATCH"]:
                    bad_files.append(rel)
                elif status == "TOLERATED":
                    warn_files.append(rel)
            else:
                same = open(pe, "rb").read() == open(po, "rb").read()
                print(f"{'IDENTICAL' if same else 'MISMATCH':9s} {rel}  (byte comparison)")
                if not same:
                    bad_files.append(rel)
    # exit codes
    le, lo = os.path.join(a.expected, "run_log.tsv"), os.path.join(a.out, "run_log.tsv")
    if os.path.exists(le):
        if not os.path.exists(lo):
            print("MISSING  run_log.tsv")
            bad_files.append("run_log.tsv")
        else:
            ce, co = read_log(le), read_log(lo)
            diff = [(k, ce[k], co.get(k)) for k in ce if co.get(k) != ce[k]
                    and not (a.allow_missing and k not in co)]
            for k, x, y in diff:
                print(f"MISMATCH exit code of {k}: expected {x}, out {y}")
            print(f"{'IDENTICAL' if not diff else 'MISMATCH':9s} run_log.tsv  (exit codes of {len(ce)} runs; "
                  f"{sum(1 for v in ce.values() if v != '0')} of them are expected to be nonzero)")
            if diff:
                bad_files.append("run_log.tsv")
    print()
    print(f"SUMMARY: {n_files} reference files compared; {len(bad_files)} with MISMATCH or MISSING; "
          f"{len(warn_files)} with tolerated HINT/FLOAT differences; {len(not_run)} not run.")
    if bad_files:
        print("RESULT: FAILED (see MISMATCH/MISSING above)")
        sys.exit(1)
    if warn_files and a.strict:
        print("RESULT: FAILED in --strict mode (tolerated differences present)")
        sys.exit(1)
    print("RESULT: OK" + (" (every compared line identical)" if not warn_files else
                          " (with tolerated HINT/FLOAT differences; verdicts identical)"))


if __name__ == "__main__":
    main()

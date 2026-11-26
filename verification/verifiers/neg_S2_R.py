"""Negative checks for the second S verifier (verify_S2.py) and for the R verifier (verify_R.py).

NEW in this package: the original negative checks for these two verifiers were run interactively and no script
was kept. This harness re-creates them so that they can be re-run; it does not change either verifier.

  verify_S2.py on corrupted copies of certificates/S/S_n4_K2_t1001.json (the n = 4 Bareiss route):
    S2-a  s below lambda_2      (s := int(E2) - 10, E2 from the informational 'bilgi' field)
    S2-b  tau tripled
    S2-c  a label of weight K + 1
  verify_R.py (it looks up certificates/R/R_n{n}_K{K}_j{j}_t{seed}.json relative to the working directory, so
  each case runs in its own directory under out/negative_S2_R/):
    R-1   R(2) at psi_8 (seed 1001), a false statement (real rank 278 < 512), with t_G = 1000, f_G = 8
    R-2   the genuine R(3) certificate at psi_8 (seed 1001) with t_G tripled
    R-3   the R(3) certificate of seed 1001 stored under the name of seed 1002 and run with the S certificate
          of seed 1002 (SHA-256 mismatch)
A case counts as REJECTED if the verifier exits with a nonzero status and its output contains no "ALL PASSED".
Run from the package root.
"""
import copy
import hashlib
import json
import os
import subprocess
import sys

ROOT = os.path.abspath(".")
OUT = os.path.join(ROOT, "out", "negative_S2_R")
ENV = dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", VECLIB_MAXIMUM_THREADS="1")


def run(args, cwd):
    r = subprocess.run([sys.executable, "-u"] + args, capture_output=True, text=True, cwd=cwd, env=ENV, timeout=280)
    out_lines = [s for s in r.stdout.splitlines() if s.strip()]
    err_lines = [s for s in r.stderr.splitlines() if s.strip()]
    rejected = r.returncode != 0 and "ALL PASSED" not in r.stdout
    last_out = out_lines[-1].strip() if out_lines else ""
    last_err = err_lines[-1].strip() if err_lines else ""
    return rejected, r.returncode, last_out, last_err


def report(name, verifier, res):
    rejected, rc, last_out, last_err = res
    print(f"{name:44s} | {verifier:12s} | {'REJECTED' if rejected else 'ACCEPTED (!)'} | exit {rc} | "
          f"last stdout line: {last_out!r} | last stderr line: {last_err!r}", flush=True)
    return rejected


def sha(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def main():
    os.makedirs(OUT, exist_ok=True)
    all_rejected = True

    # --- verify_S2.py
    s4_path = os.path.join(ROOT, "certificates", "S", "S_n4_K2_t1001.json")
    s4 = json.load(open(s4_path))
    n, K = s4["n"], s4["K"]
    cases = [
        ("S2-a s < λ₂ (s = int(E2) − 10)", dict(s=int(s4["bilgi"]["E2"]) - 10)),
        ("S2-b τ ×3", dict(tau=3 * s4["tau"])),
        ("S2-c label of weight K+1", dict(etiketler=["X" * (K + 1) + "I" * (n - K - 1)] + s4["etiketler"][1:])),
    ]
    for i, (name, change) in enumerate(cases):
        c = copy.deepcopy(s4)
        c.update(change)
        p = os.path.join(OUT, f"S2_case{i + 1}.json")
        with open(p, "w") as fh:
            json.dump(c, fh)
        res = run([os.path.join(ROOT, "verifiers", "verify_S2.py"), p], ROOT)
        all_rejected &= report(name, "verify_S2", res)

    # --- verify_R.py
    s8_path = os.path.join(ROOT, "certificates", "S", "S_n8_K3_t1001.json")
    s8b_path = os.path.join(ROOT, "certificates", "S", "S_n8_K3_t1002.json")
    r3 = json.load(open(os.path.join(ROOT, "certificates", "R", "R_n8_K3_j3_t1001.json")))
    r_cases = [
        ("R-1 R(2) at ψ8, false (278 < 512), t_G = 1000", "R1", "R_n8_K3_j2_t1001.json",
         {"aciklama": "Corrupted R certificate (negative test): R(2) at psi_8 is false.",
          "u1_sertifika": "certificates/S/S_n8_K3_t1001.json", "u1_sha256": sha(s8_path),
          "n": 8, "j": 2, "t_G": 1000, "f_G": 8}, s8_path, 2),
        ("R-2 genuine R(3) at ψ8 with t_G ×3", "R2", "R_n8_K3_j3_t1001.json",
         dict(r3, t_G=3 * r3["t_G"]), s8_path, 3),
        ("R-3 seed-1001 R(3) used for seed 1002 (sha256)", "R3", "R_n8_K3_j3_t1002.json",
         r3, s8b_path, 3),
    ]
    for name, sub, fname, cert, s_path, j in r_cases:
        d = os.path.join(OUT, sub, "certificates", "R")
        os.makedirs(d, exist_ok=True)
        with open(os.path.join(d, fname), "w") as fh:
            json.dump(cert, fh, ensure_ascii=False, indent=1)
        res = run([os.path.join(ROOT, "verifiers", "verify_R.py"), s_path, str(j)], os.path.join(OUT, sub))
        all_rejected &= report(name, "verify_R", res)

    print("NEGATIVE CHECK RESULT (verify_S2, verify_R):", "all rejected" if all_rejected else "AT LEAST ONE ACCEPTED — PROBLEM")
    sys.exit(0 if all_rejected else 1)


if __name__ == "__main__":
    main()

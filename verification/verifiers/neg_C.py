"""Negative checks: both C verifiers must REJECT corrupted C certificates.
The corrupted copies are written to out/negative_C/ (the shipped certificates are not touched).
Run from the package root; `python3` on the PATH must be the interpreter of the pinned environment.
"""
import json, hashlib, subprocess, os, sys, copy
from fractions import Fraction

KOK = "."
NEG = f"{KOK}/out/negative_C"
os.makedirs(NEG, exist_ok=True)
ORT = dict(os.environ, OPENBLAS_NUM_THREADS="1", OMP_NUM_THREADS="1", VECLIB_MAXIMUM_THREADS="1")


def yaz_u1(U, ad):
    yol = f"{NEG}/{ad}"
    with open(yol, "w") as f:
        json.dump(U, f)
    return yol, hashlib.sha256(open(yol, "rb").read()).hexdigest()


def yaz_C(Cc, ad):
    yol = f"{NEG}/{ad}"
    json.dump(Cc, open(yol, "w"), ensure_ascii=False)
    return yol


def kos(cyol):
    out = []
    for v in ["verify_C1.py", "verify_C2.py"]:
        r = subprocess.run(["nice", "-n", "15", "python3", "-u", f"{KOK}/verifiers/{v}", cyol], capture_output=True, text=True,
                           env=ORT, timeout=280)
        son = [s for s in r.stdout.splitlines() if "FAILED" in s or "ALL PASSED" in s]
        out.append((v, r.returncode, son[-1] if son else (r.stderr.strip().splitlines() or ["?"])[-1]))
    return out


def main():
    base8 = json.load(open(f"{KOK}/certificates/C/C_n8_K3_Kp2_t1001.json"))
    U8 = json.load(open(base8["u1_sertifika"]))
    base4 = json.load(open(f"{KOK}/certificates/C/C_n4_K2_Kp2_t1001.json"))
    U4 = json.load(open(base4["u1_sertifika"]))
    vakalar = []
    # N1: claim C(8,1) (a false statement: rank 25 < 256)
    c = dict(base8, Kp=1); vakalar.append(("N1 C(8,1) (false: 25 < 256)", yaz_C(c, "N1.json")))
    # N2: t_G tripled (above lambda_min)
    c = dict(base8, t_G=3 * base8["t_G"]); vakalar.append(("N2 t_G ×3", yaz_C(c, "N2.json")))
    # N3: sign of every 7th component of w flipped
    U = copy.deepcopy(U8); U["w"] = [[-a, -b] if k % 7 == 0 else [a, b] for k, (a, b) in enumerate(U["w"])]
    y, h = yaz_u1(U, "N3_u1.json"); c = dict(base8, u1_sertifika=y, u1_sha256=h)
    vakalar.append(("N3 w corrupted (every 7th entry −)", yaz_C(c, "N3.json")))
    # N4: s >= theta
    U = copy.deepcopy(U8); U["s"] = 1641195
    y, h = yaz_u1(U, "N4_u1.json"); c = dict(base8, u1_sertifika=y, u1_sha256=h)
    vakalar.append(("N4 s = 1641195 > θ", yaz_C(c, "N4.json")))
    # N5: s < lambda_2 (lambda_2 ~ 1544446.5)
    U = copy.deepcopy(U8); U["s"] = 1540000
    y, h = yaz_u1(U, "N5_u1.json"); c = dict(base8, u1_sertifika=y, u1_sha256=h)
    vakalar.append(("N5 s = 1540000 < λ₂", yaz_C(c, "N5.json")))
    # N6: sign of the largest |c| coefficient flipped
    U = copy.deepcopy(U8); k = max(range(len(U["katsayilar"])), key=lambda i: abs(U["katsayilar"][i]))
    U["katsayilar"][k] = -U["katsayilar"][k]
    y, h = yaz_u1(U, "N6_u1.json"); c = dict(base8, u1_sertifika=y, u1_sha256=h)
    vakalar.append((f"N6 sign of c[{U['etiketler'][k]}] flipped", yaz_C(c, "N6.json")))
    # N7: w of another seed (t1002) with the H of t1001
    U = copy.deepcopy(U8); U["w"] = json.load(open(base8["u1_sertifika"].replace("t1001", "t1002")))["w"]
    y, h = yaz_u1(U, "N7_u1.json"); c = dict(base8, u1_sertifika=y, u1_sha256=h)
    vakalar.append(("N7 w ← seed 1002 (H of seed 1001)", yaz_C(c, "N7.json")))
    # N8: sha256 mismatch (S file changed, the C certificate still carries the old hash)
    c = dict(base8, u1_sertifika=f"{NEG}/N6_u1.json")
    vakalar.append(("N8 sha256 mismatch", yaz_C(c, "N8.json")))
    # N9: n = 4, t_G tripled (Bareiss route of verify_C2)
    c = dict(base4, t_G=3 * base4["t_G"]); vakalar.append(("N9 n=4 t_G ×3 (Bareiss route)", yaz_C(c, "N9.json")))
    # N10: n = 4, C(4,1) (false: 13 < 16)
    c = dict(base4, Kp=1); vakalar.append(("N10 C(4,1) (false: 13 < 16)", yaz_C(c, "N10.json")))
    # N11: int64 overflow attack: entries of z ~ 2^31.5 => z^dag z wraps in int64
    U = copy.deepcopy(U8); U["z"] = [[3037000500, -3037000500] for _ in U["z"]]
    y, h = yaz_u1(U, "N11_u1.json"); c = dict(base8, u1_sertifika=y, u1_sha256=h)
    vakalar.append(("N11 z ~ 2^31.5 (z†z int64 overflow)", yaz_C(c, "N11.json")))
    # N12: entries of w times 2^21 => partial sums of G and Hw exceed int64
    U = copy.deepcopy(U8); U["w"] = [[a << 21, b << 21] for a, b in U["w"]]
    y, h = yaz_u1(U, "N12_u1.json"); c = dict(base8, u1_sertifika=y, u1_sha256=h)
    vakalar.append(("N12 w × 2^21 (G/Hw int64 overflow)", yaz_C(c, "N12.json")))
    hepsi = True
    for ad, yol in vakalar:
        for v, rc, son in kos(yol):
            red = rc != 0 and "PASSED" not in son
            hepsi &= red
            print(f"{ad:42s} | {v:18s} | {'REJECTED' if red else 'ACCEPTED (!)'} | {son}", flush=True)
    print("NEGATIVE CHECK RESULT:", "all rejected" if hepsi else "AT LEAST ONE ACCEPTED — PROBLEM")


if __name__ == "__main__":
    main()

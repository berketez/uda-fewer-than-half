"""Tests of the S verifier: (i) the bit-mask Pauli construction equals the explicit Kronecker product;
(ii) corrupted certificates are REJECTED.
The original harness was written for the first version of the S verifier; in this package it imports and runs
the final version verify_S_v3.py (the only S verifier version shipped). The test logic is unchanged.
Usage: python3 neg_S_v3.py certificates/S/S_n8_K3_t1001.json
"""
import sys, json, subprocess, itertools, os, tempfile
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import verify_S_v3 as V

# (i) Kronecker check: n = 3, all 64 Paulis; qubit j = bit j of x => in the Kronecker order the most significant bit comes first
tek = {"I": np.eye(2), "X": np.array([[0, 1], [1, 0]]), "Z": np.diag([1, -1]),
       "Y": np.array([[0, -1j], [1j, 0]])}
n, D = 3, 8
x = np.arange(D)
pc = np.array([bin(i).count("1") for i in range(D)])
hata = 0.0
for harfler in itertools.product("IXYZ", repeat=n):
    e = "".join(harfler)
    P = np.array([[1.0]])
    for j in reversed(range(n)):
        P = np.kron(P, tek[e[j]])
    a, b, ny = V.maske(e)
    sgn = 1 - 2 * (pc[b & x] & 1)
    ur, ui = V.i_kuvvet(ny, sgn, np.zeros(D, dtype=np.int64))
    Q = np.zeros((D, D), complex)
    Q[x ^ a, x] = ur + 1j * ui
    hata = max(hata, np.abs(P - Q).max())
print(f"(i) Kronecker check (n = 3, 64 Paulis): max |difference| = {hata}")

# (ii) corrupted certificates
asil = json.load(open(sys.argv[1]))
E1 = asil["bilgi"]["E1"]; E2 = asil["bilgi"]["E2"]
bozuk = {
    "s > λ₁ (D1 must fail)": dict(s=int(E1) + 10),
    "s < λ₂ (D2 must fail)": dict(s=int(E2) - 10),
    "label of weight K+1 (D0 must fail)": dict(etiketler=["X" * (asil["K"] + 1) + "I" * (asil["n"] - asil["K"] - 1)]
                                         + asil["etiketler"][1:]),
    "τ too large (D3 must fail)": dict(tau=asil["tau"] * 3),
    "w coarse (D4 must fail)": dict(w=[[u >> 12, v >> 12] for u, v in asil["w"]], tau=asil["tau"] >> 25),
}
for ad, deg in bozuk.items():
    C = dict(asil); C.update(deg)
    with tempfile.NamedTemporaryFile("w", suffix=".json", delete=False) as fh:
        json.dump(C, fh); yol = fh.name
    r = subprocess.run([sys.executable, os.path.join(os.path.dirname(os.path.abspath(__file__)), "verify_S_v3.py"), yol],
                       capture_output=True, text=True)
    son = [s for s in r.stdout.splitlines() if s.startswith("FAILED") or s.startswith("ALL PASSED")]
    print(f"(ii) {ad}: exit code {r.returncode}; {son[-1] if son else r.stderr.strip()[-200:]}")
    os.unlink(yol)

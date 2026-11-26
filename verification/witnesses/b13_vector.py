"""The b = 13 witness vector of the paper (Sec. "Exact certificates", modular rank witnesses).

NEW in this package (no original script). It rebuilds v exactly as fp_witness.py does in its modes
`simetrik` / `sektor` for b = 13 and seed 1:
    u = numpy.random.default_rng(1).integers(0, 2, size=8192)        (NumPy 1.26.4, PCG64)
    v_x = u_x * [popcount(x) even]
and prints ||v||^2 and the SHA-256 hash of the ASCII bit string v_0 v_1 ... v_8191, so that the vector used in
the rank computation can be compared with the values quoted in the paper (||v||^2 = 2091 and the hash).
"""
import hashlib

import numpy as np

b = 13
D = 1 << b
pc = np.zeros(D, dtype=np.int64)
for k in range(1, D):
    pc[k] = pc[k >> 1] + (k & 1)
rng = np.random.default_rng(1)
v = rng.integers(0, 2, size=D).astype(np.int64) * (1 - (pc & 1))
bits = "".join(str(int(t)) for t in v)
assert len(bits) == D and set(bits) <= {"0", "1"}
print(f"b = {b}, seed = 1: numpy {np.__version__}")
print(f"||v||^2 = {int(v.sum())} (number of ones; v has support only on even-parity x: "
      f"{int(v[pc % 2 == 1].sum()) == 0})")
print(f"SHA-256 of the ASCII bit string v_0...v_{D - 1}: {hashlib.sha256(bits.encode('ascii')).hexdigest()}")

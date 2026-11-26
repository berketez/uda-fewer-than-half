# uda-verification 1.0.0

Verification package for the paper

> B. Tezgöçen, *Pure qubit states determined by marginals on fewer than half of the qubits: a measure-one bound and a
> correction to the Jones–Linden lower bound* (2026).

The identifier of the paper (arXiv and/or journal) is listed under "Related identifiers" on the Zenodo record of
this package.

The package re-runs every computer-assisted step of the paper on your own machine and compares the result with the
reference outputs in `expected/`, which were produced with the commands below (Python 3.12.7, NumPy 1.26.4).
`CLAIMS.md` maps each computer-assisted statement of the paper to a command, an output file and the line to look at.

## What is checked here, and what is not

Checked by computation (details and commands in `CLAIMS.md`):

- **Theorem 3 (finite certificates).** The seven S(n,K) certificates — (4,2), (6,3), (8,3) with three seeds,
  (10,4), (12,4) — pass the final S verifier `verifiers/verify_S_v3.py` (Table "S certificates" of the paper).
  The five certificates with n ≤ 8 also pass the second S verifier `verifiers/verify_S2.py`.
- **Inputs of Theorem 2 and of the gluing route.** C(2) at n = 4, 6, 8 (three seeds) and C(3) at n = 10 pass both
  C verifiers; R(2) at n = 4, 6, R(3) at n = 8 (three seeds) and R(3) at n = 10 pass the R verifier.
- **Finite-field witnesses (Table "Generic C(b,c) witnesses").** Rank D over F_p for b = 2, …, 13, the C(8,2)
  witness quoted in the paper (determinant 62 mod 1009, ranks over F_1009, F_1013, F_10009) checked by two separate
  codes, and the norm and SHA-256 hash of the b = 13 witness vector.
- **Dynamic programming (Theorem 2(ii), Appendix "Dynamic-programming values").** The bounds (3n+24)/13 for all n and
  (3n+20)/13 for n ≥ 14, the (4,4,3) block at n = 13, the table for n ≤ 26, the list of n where the bound equals the
  counting bound, the chain of Theorem 2′, and the same DP without the S certificates.
- **Theorem 1 explicit thresholds (Table "Thresholds of Theorem 1").** Exact integer checks behind N0 = 139, 996,
  1654 and 274, the margin and tail numbers quoted below the table, and the constants κ_c, f′(κ_c),
  f(0.195) − 1, g(5000) (these constants are computed in floating point; the thresholds themselves rest on the
  integer checks and on the analytic tail bounds of the paper). The three example values of the optimised
  construction quoted in the paper (K = 93, 399, 1161 at n = 200, 1000, 3000) are checked in exact integers for the
  chosen (t, L) (`thresholds/examples_exact.py`; see limitation 9 for what this does and does not show).
- **The proposition marked "computer-assisted" (n ≥ 83).** The arithmetic of 2c(n)+1 < n/2 (last failure at
  n = 82, scan n ≤ 400).
- **Two remarks** (indicative only, not used in any proof): "none of 1500 random Lagrangians had covering radius ≤ 2
  at m = 8" (exact combinatorics on a pseudo-random sample) and "ψ8 ⊗ ψ4 at K = 3: rank 4286/8192" (floating point).
- **Negative checks.** Corrupted S, C and R certificates are rejected; the final S verifier rejects the overflow
  counterexample `certificates/negative/S_overflow_p.json`; the `--blas` mode refuses certificates for which its
  exactness bound does not hold.

Not checked here: the analytic parts of the proofs (Lemmas 1–3, Lemma A, Lemma B, Lemma B′, the asymptotic
statements of Theorems 1 and 2, the counting proposition), statements quoted from the literature (e.g. the uniform
states in the Observation of Sec. "Definitions and thresholds"), and the literature search. The certificates establish the numerical hypotheses of these lemmas;
that the lemmas imply the theorems is a mathematical argument in the paper, not a computation. Theorem 2(i) gives no
explicit constant, so there is nothing to compute for it.

## Environment

- Python 3.12.7 and NumPy 1.26.4 (the versions used for `expected/`). No other package is needed.
- Every run is single-threaded: `run_all.sh` sets `OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1
  VECLIB_MAXIMUM_THREADS=1 MKL_NUM_THREADS=1` and runs each job with `nice -n 15`. With a multi-threaded BLAS and
  several jobs at once a laptop can become unresponsive.
- `python3` on the PATH must be this interpreter (one harness, `verifiers/neg_C.py`, calls `python3` itself).
- The reference outputs were produced on macOS (Apple silicon) with the NumPy 1.26.4 wheel's OpenBLAS (64-bit
  integer interface).

Example set-up:

```
python3.12 -m venv venv
. venv/bin/activate
pip install numpy==1.26.4
```

## Running

```
./run_all.sh            # everything, writes out/ (see the timing table below)
python3 compare.py      # compares out/ with expected/
```

Each run is stopped after `RUN_TIMEOUT` seconds (default 1800, `RUN_TIMEOUT=0 ./run_all.sh` disables the limit);
the longest run took 365 s on the reference laptop.

`./run_all.sh --quick` skips the heavy runs (the n = 10 and n = 12 certificates, the b = 12 and b = 13 witnesses and
the numerical remark, which needs several GB of memory); afterwards use `python3 compare.py --allow-missing`.

All commands are run from the package root (`run_all.sh` changes to it itself); several scripts resolve paths
such as `certificates/...` relative to the working directory. Single runs can be repeated with the commands listed in
`CLAIMS.md`, e.g. `python3 verifiers/verify_S_v3.py certificates/S/S_n8_K3_t1001.json`.

`compare.py` checks that every reference file exists in `out/`, that every line agrees after masking wall-clock
times, that the generated corrupted certificates are byte-identical, and that every run has the expected exit status
(`out/run_log.tsv`; several negative checks exit with status 1 by design). On a machine with a different BLAS/LAPACK
build two kinds of difference are tolerated and listed: numbers that depend on the floating-point Cholesky *hint* of
the exact verifiers (the residual ‖E‖, the ratio next to it and the certified lower bounds derived from it; the
verdict must still be the same), and the last digits of floating-point display values of three non-verifier scripts.
`python3 compare.py --strict` fails on any difference.

### Time and memory (measured for `expected/`)

| Run | Wall-clock | Peak memory |
|---|---|---|
| 63 light runs together (longest: `thm1_constants`, 18 s) | 2.5 min | ≤ 190 MiB |
| `S_v3_n10_K4_t1001` | 365 s | 447 MiB |
| `S_v3_n12_K4_t1001_blas` | 139 s | 4.8 GiB |
| `C1_n10_K4_Kp3_t1001` | 14 s | 605 MiB |
| `C2_n10_K4_Kp3_t1001` | 11 s | 251 MiB |
| `R_n10_K4_j3_t1001` | 14 s | 695 MiB |
| `fp_simetrik_b12_c3` | 64 s | 445 MiB |
| `fp_sektor_b13_c3_cift` | 121 s | 237 MiB |
| `fp_sektor_b13_c3_tek` | 112 s | 248 MiB |
| `numerics_glue_8x4_K3_K4` | 128 s | 3.5 GiB |

The heavy runs execute in two parallel lanes (lane A: the n = 10 runs; lane B: n = 12, b = 12, 13 and the numerical remark), so the total wall-clock time is the light part plus the longer lane. The reference run was made on a laptop (Apple silicon) while other jobs were running; every job was single-threaded and niced. Per-run figures: `expected/resources.tsv`.

## Layout

```
certificates/S/        S(n,K) certificates (byte-identical to the originals)
certificates/C/        C(n,K') certificates (only the path field "u1_sertifika" was changed)
certificates/R/        R(j) certificates (only the path field "u1_sertifika" was changed)
certificates/negative/ the overflow counterexample for the S verifier
verifiers/             verify_S_v3.py, verify_S2.py, verify_C1.py, verify_C2.py, verify_R.py and the negative checks neg_*.py
witnesses/             fp_witness.py (F_p rank witnesses), c82_independent.py, b13_vector.py, fp_witness_selftest.py
thresholds/            thm1_constants.py, n0_exact.py, examples_exact.py, n0_log_margin.py, prop_half83.py, dp_glue.py,
                       dp_no_S.py, dp_qubit_chain.py, lemma23.py, lagrangian_cover.py
numerics/              direct_glue_rank.py (floating point, indicative)
expected/              reference outputs of ./run_all.sh, including run_log.tsv and the generated corrupted certificates
tools/                 ast_equiv.py, json_equiv.py and their file lists (provenance checks; need the original files)
provenance/            output of tools/ast_equiv.py and tools/json_equiv.py
run_all.sh, compare.py, CLAIMS.md, MANIFEST.md, SHA256SUMS, LICENSE
```

`sha256sum -c SHA256SUMS` (Linux) or `shasum -a 256 -c SHA256SUMS` (macOS) checks the integrity of every file.

## Certificate format and conventions

A Pauli label is a string over `IXYZ`; `label[j]` acts on qubit j, and in the computational basis |x⟩ qubit j is
bit j of x (P|x⟩ = i^{#Y} (−1)^{popcount(b∧x)} |x ⊕ a⟩ with the X/Z bit masks a, b). An S certificate stores an
integer Hamiltonian H = Σ c_P P and integer data (s, q, z, t_A, f_A, w, τ, f_G) for the checks D0–D4 of the paper:
the state ψ0 is *defined* as the top eigenvector of H and is never written down. A C or R certificate stores the
positivity parameters (t_G, f_G) of its Gram matrix and refers to its S certificate by path and by SHA-256.

The free-text field `aciklama` of the certificates is in Turkish and is not read by any verifier. The S certificates
say: "U1 exact UDA certificate. Label: label[j] acts on qubit j; in the |x⟩ basis qubit j = bit j of x. All numbers
are integers; the field 'bilgi' is informational only, the verifier does not use it." The C and R certificates say:
"U8 C(n,K′) certificate: parameters t_G, f_G. Read together with the U1 certificate (sha256)." and "U8 R(j)
certificate (t, f). Read with the U1 certificate (sha256)." The S certificates are kept byte-identical because the
C and R certificates bind them by SHA-256.

## Glossary (identifiers kept from the original code)

The scripts are English translations of the original research scripts. Messages, comments and docstrings were
translated; variable and function names, command words and JSON keys were kept so that the logic is provably
unchanged (see Provenance). The Turkish words that remain:

| Word | Meaning | Where |
|---|---|---|
| `etiketler`, `katsayilar` | labels, coefficients (of H) | JSON keys |
| `aciklama`, `bilgi` | description; informational data (not used by the verifiers) | JSON keys |
| `tohum` | seed; the `t1001` in file names is seed 1001 | JSON key, file names |
| `u1_sertifika`, `u1_sha256` | path and SHA-256 of the underlying S certificate ("U1" and "U8" are the labels of the S and C/R certificate families in the original workflow) | C/R JSON keys |
| `Kp`, `j`, `t_G`, `f_G` | level K′ of C(n,K′), level j of R(j), positivity parameters | C/R JSON keys |
| `hakem` | "referee": the C(8,2) witness quoted in the paper | `fp_witness.py` mode |
| `rastgele` | random 0/1 witness | `fp_witness.py` mode |
| `simetrik` | Z^{⊗b}-symmetric witness (two parity sectors) | `fp_witness.py` mode |
| `sektor`, `cift`, `tek`, `ikisi` | one sector; even; odd; both | `fp_witness.py` mode and arguments |
| `a`, `b`, `c` | the three checks of `n0_exact.py` (optimised (t,L); t = 7 row; logarithmic row) | `n0_exact.py` mode |
| `V0`, `V1`, `V2` | variants of the dynamic programme; V2 is the one used in the paper | `dp_glue.py` output |
| `K_say`, `c_say` | counting bounds K_count(n) and the analogous bound for C | DP output |
| `gram`, `svd`, `ikisi`, `ongoru` | methods of `direct_glue_rank.py` (both; prediction by Lemma B′) | arguments |
| `--uret` | "generate" (parameter generation of `verify_R.py`; not used) | option |
| `dur`, `psd_kesin` | "stop" (the failure helper); exact positivity routine | function names |

## Known limitations

These are the weak points stated in the appendix "Verifiers" of the paper, plus points noticed while assembling the
package.

1. All verifiers were written within a single AI-assisted workflow, in one language (Python/NumPy). The two S
   verifiers and the two C verifiers use different constructions of the Pauli operators and different positivity
   proofs, but they are not independent in authorship. An independent verifier in another language (e.g. FLINT) would
   close this point.
2. The second S verifier `verify_S2.py` covers only n ≤ 8. The n = 12 certificate is checked by the final verifier
   alone. For n = 10 the gap λ₁ > s > λ₂ (checks D1–D2) is re-proved by `verify_C1.py` (and, with the same code, by
   `verify_R.py`), but the rank condition R(4) (checks D3–D4) only by the final verifier. `verify_S2.py` checks some int64 bounds but not all
   (none for the construction of H and A, and p = z†z is summed in int64); it is a cross-check of the shipped
   certificates, not a verifier hardened against adversarial input.
3. Exactness of NumPy int64 matrix products in the absence of overflow is assumed. The verifiers prove explicit bounds
   (|partial sum| < 2^62) before every int64 product and spot-check entries with Python integers.
4. The `--blas` mode (used for n = 12) computes integer products with floating-point GEMM after proving that every
   partial sum is below 2^53. It assumes that GEMM uses only additions and multiplications of the inputs
   (no Strassen-type or reduced-precision algorithm). Randomly chosen entries are recomputed with Python integers
   (32 per positivity check and 36 of the Gram matrix G).
5. The F_p witnesses use one elimination code (`fp_witness.py`). It is cross-checked by a self-test on matrices of
   planted rank (`fp_witness_selftest.py`) and, for C(8,2), by a separately coded rank and determinant computation
   (`c82_independent.py`).
6. The dynamic programme takes the witnessed values c_gen(b) and the block data of the exact certificates as inputs;
   these inputs are established by the separate runs listed in `CLAIMS.md`, not inside `dp_glue.py`.
7. Two overflow gaps were found and fixed during the work; the earlier verifier versions are not included. The package
   only shows that the final version rejects the counterexample and the overflow sweep. Earlier negative checks of
   `verify_S2.py` and `verify_R.py` were not scripted; `verifiers/neg_S2_R.py` is new and re-creates them.
8. The two remarks (`thresholds/lagrangian_cover.py`, a pseudo-random sample; `numerics/direct_glue_rank.py`,
   floating point) are indicative and are not used in any proof.
9. The example values of the optimised construction quoted in the paper (K = 93 at n = 200, 399 at n = 1000, 1161 at
   n = 3000) are confirmed in exact integers by `thresholds/examples_exact.py`: for the chosen (t, L) =
   (6, 40), (9, 190), (9, 571), condition (*) holds and fails for L − 1, so L is the smallest valid L for the chosen
   t. The choice of t itself, i.e. that no other t gives a smaller K, rests on the floating-point hint of the search
   (the same rule as `n0_exact.py a`); it is not proven in integers. The example values are an illustration and no
   threshold depends on them.

## Provenance

Every script except `verifiers/neg_S2_R.py`, `witnesses/b13_vector.py` and `thresholds/examples_exact.py` (new,
marked as such in their docstrings)
is a translated copy of an original research script. `tools/ast_equiv.py` compares each pair: after removing
docstrings and replacing every string constant by a placeholder, the two abstract syntax trees are identical; every
changed string is listed with its role, and changes outside printed messages (file paths, the strings that the negative
checks search for in the translated output, labels of test cases) are flagged. The report is
`provenance/ast_equiv_report.txt`; `provenance/json_equiv_report.txt` shows that the S certificates are byte-identical
to the originals and that the C/R certificates and the counterexample differ only in the declared fields. Both
tools need the original files and therefore cannot be re-run from this package alone. `MANIFEST.md` lists the original
location and both SHA-256 hashes of every file.

The use of AI in this work is described in the statement on the use of AI in the paper.

## Licence and citation

Code: MIT; data and documentation: CC BY 4.0 (see `LICENSE`). Please cite the paper and this package; the DOI of
the package is the one shown on its Zenodo record.

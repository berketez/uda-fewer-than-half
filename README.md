# Pure qubit states determined by marginals on fewer than half of the qubits

**A measure-one bound and a correction to the Jones–Linden lower bound**

Berke Tezgöçen · November 2026

[Paper (English, PDF)](paper/uda_en.pdf) · [Makale (Türkçe, PDF)](paper/uda_tr.pdf) · [Lean 4 proof](lean/) · [Verification package](verification/)

> **Status.** Theorem 1 (all thresholds and the asymptotic form), Lemmas 1–3 and A, the small
> cases of Theorem 3 and the upper bound of Theorem 2 are **formally verified in Lean 4 with
> Mathlib**: no `sorry`, only the three standard axioms, and anyone can rebuild it (see
> [`lean/`](lean/)). The large certificates of Theorem 3, the explicit bound of Theorem 2 (ii) and
> the lower bounds have been checked only by AI readings and exact-arithmetic verifiers. No human
> expert has checked the proofs yet. Comments, checks and objections are welcome (open an issue).

---

## Abstract

How much of a many-qubit pure state is written in its small parts? A pure $n$-qubit state is *uniquely determined
among all states* (UDA) by its $K$-body marginals if no other density matrix, pure or mixed, has the same reduced
states on every set of $K$ qubits. In 2005 Jones and Linden asserted that the marginals of fewer than half of the
parties are insufficient for almost all states. This lower-bound statement is still quoted in the literature on the
quantum marginal problem.

We show that the opposite is true for qubits. **Haar-almost every $n$-qubit pure state is UDA by its
$K(n)$-body marginals with $K(n) = 2\kappa_c n + O(\log n) \approx 0.379\,n$**, where $\kappa_c \approx 0.189$ is the
root of $h_2(\kappa) + \kappa \log_2 3 = 1$. Explicitly, marginals on fewer than half of the qubits suffice for every
$n \ge 139$, and $\lceil 0.4n \rceil$-body marginals suffice for every $n \ge 996$. Such a state is moreover the
unique ground state, with energy zero, of a positive semidefinite $K(n)$-local Hamiltonian. The proof combines Pauli
spanning, the covering radius of stabilizer states, and polynomial genericity.

For the smallest $K$ at which UDA states form a set of positive measure we show $`K^{\ast}_{+}(n) = \kappa_c n + O(\log n)`$,
so the leading coefficient of this threshold equals the parameter-counting coefficient of Linden and Wootters (2002);
explicitly $`\kappa_c n \lt K^{\ast}_{+}(n) \le (3n+24)/13`$ for every $n$. For $(n,K) = (8,3), (10,4), (12,4)$ we give open
sets of UDA states whose certificates are verified by exact integer and rational inequalities.

Consequently, for qubits the Jones–Linden lower-bound statement fails for every $N \ge 7$, and for every $N \ge 139$
the opposite statement holds for almost every state. Their upper bound is unaffected. We locate the invalid step in
their argument: an equation count for a real quadratic system is taken as proof of a real family of solutions,
which does not follow (the simplest counterexample is $x^2 + y^2 = 0$).

## Main results

| | Statement | How it is established |
|---|---|---|
| **Theorem 1** (measure one) | Haar-almost every pure state is $K(n)$-UDA and the unique zero-energy ground state of a PSD $K(n)$-local Hamiltonian; $K(n) = 2\kappa_c n + O(\log n)$ | analytic proof; explicit thresholds by exact integer checks |
| | $K(n) = \lceil n/2 \rceil - 1$ (fewer than half) for every $n \ge 139$ | |
| | $K(n) = \lceil 0.4n \rceil$ for every $n \ge 996$ | |
| | $K(n) = \lceil 2\kappa_c n + 4\log_2 n \rceil$ for every $n \ge 274$ | |
| **Theorem 2** (positive measure) | $`K^{\ast}_{+}(n) = \kappa_c n + O(\log n)`$; $`\ \kappa_c n \lt K^{\ast}_{+}(n) \le (3n+24)/13`$ for all $n$ | analytic proof + gluing of exact certificates |
| **Theorem 3** (finite certificates) | open sets of UDA states at $(n,K) = (8,3), (10,4), (12,4)$ with $K \lt  n/2$, and $(4,2), (6,3)$ with $K = n/2$ | computer-assisted; every final verdict is an exact integer or rational inequality |
| **Correction** | the Jones–Linden lower bound fails for qubits for every $N \ge 7$ (positive measure) and every $N \ge 139$ (measure one) | Theorems 1–3; Sec. "Where the Jones–Linden argument fails" |

## What we do not claim

- Not that almost every state is determined by marginals on fewer than half of its qubits for *small* $n$: this is
  false at $(n,K) = (8,3)$, where a 3-uniform graph state has a non-UDA neighbourhood.
- Not that the measure-one threshold is $\kappa_c n + O(\log n)$: between the lower bound $\kappa_c n$ and our upper
  bound $2\kappa_c n$ a factor of 2 remains open.
- No radii or volumes for the open sets of Theorems 2 and 3, and nothing about measurement cost, statistical cost or
  robustness to noise. All results concern determinability from exact marginals.

## Formal verification in Lean 4

The results below are proved in Lean 4 with Mathlib (`lean/`, 27 files, about 5,000 lines). The
main statement, in [`lean/UDA/Statement.lean`](lean/UDA/Statement.lean):

```lean
def MainStatement : Prop :=
  ∀ n : ℕ, 139 ≤ n →
    ∀ᵐ (ψ : Metric.sphere (0 : StateSpace n) 1) ∂(volume : Measure (StateSpace n)).toSphere,
      IsUDA n ((n + 1) / 2 - 1) (ψ : StateSpace n).ofLp ∧
        IsUGS n ((n + 1) / 2 - 1) (ψ : StateSpace n).ofLp
```

In words: for every `n ≥ 139`, almost every unit vector of `ℂ^(2^n)` (uniform sphere measure,
i.e. Haar-random pure states) is uniquely determined among all density matrices by its marginals
on all `⌈n/2⌉ − 1`-element sets of qubits, and is the unique zero-energy ground state of a positive
semidefinite `(⌈n/2⌉ − 1)`-local Hamiltonian. All definitions (Pauli operators, partial traces,
density matrices, UDA) are in [`lean/UDA/Defs.lean`](lean/UDA/Defs.lean).

Also proved:

| Lean statement | Content |
|---|---|
| `Thm1FourTenths`, `Thm1Kappa`, `Thm1Asymptotic` | Theorem 1 with `⌈0.4n⌉` (`n ≥ 996`), `⌈2κ_c n + 4 log₂ n⌉` (`n ≥ 274`), and `2κ_c n + O(log n)` |
| `KappaCStatement` | `κ_c` exists, is unique, and `0.1892896 < κ_c < 0.1892897` |
| `JonesLindenFails` | for every `N ≥ 139` there is `K < N/2` whose `K`-UDA states have positive measure and a null complement |
| `JonesLindenFailsSmall` | positive measure of `K`-UDA states at `(N, K) = (8, 3)`, `(4, 2)`, `(6, 3)` |
| `Lemma1Statement`, `GenericityStatement`, `Lemma3Statement` | Lemmas 1–3 |
| `PropTopStatement`, `LemmaAStatement` | simple top eigenvectors are UDA; Lemma A (certificate to open set) |
| `Thm3Small` | Theorem 3 for `(4, 2)`, `(6, 3)`, `(8, 3)` |
| `Thm2Upper` | Theorem 2 (i), upper bound `κ_c n + O(log n)` |

Not formalized: Theorem 3 for `(10, 4)` and `(12, 4)` and the large certificates (too large for the
Lean kernel; see `verification/`), the explicit bound of Theorem 2 (ii), and the lower bounds.

To check it yourself, install [elan](https://github.com/leanprover/elan), then:

```bash
cd lean
lake exe cache get
lake build
```

The build prints `[propext, Classical.choice, Quot.sound]` as the axioms of each of the 14 main
theorems. Details, the file map and the differences from the paper's proofs:
[`lean/README.md`](lean/README.md).

## Repository contents

```
paper/uda_en.tex, uda_en.pdf    English paper (12 pages, revtex4-2, pdflatex)
paper/uda_tr.tex, uda_tr.pdf    Turkish version of the same paper
lean/                           Lean 4 + Mathlib formalization (Theorem 1, Lemmas 1–3 and A, small cases of
                                Theorem 3, upper bound of Theorem 2)
verification/                   uda-verification 1.0.0: certificates, exact verifiers, finite-field
                                witnesses, threshold checks, reference outputs (see verification/README.md)
```

The verification package is byte-identical to its audited release; `shasum -a 256 -c SHA256SUMS` (macOS) or
`sha256sum -c SHA256SUMS` (Linux) inside `verification/` checks every file. `verification/CLAIMS.md` maps each
computer-assisted statement of the paper to a command, an output file and the line to look at.

## Reproducing the computer-assisted parts

Requires Python 3.12 and NumPy 1.26.4, nothing else.

```bash
cd verification
python3.12 -m venv venv && . venv/bin/activate && pip install numpy==1.26.4
./run_all.sh               # full run, about 10–15 min on a laptop, single runs need up to ~5 GB memory
python3 compare.py         # compare out/ with the reference outputs in expected/
# ./run_all.sh --quick && python3 compare.py --allow-missing   # light runs only
```

What is and is not checked by computation is listed in `verification/README.md`. The analytic parts of the proofs
(Lemmas 1–3, Lemma A, Lemma B, the asymptotic statements) are mathematical arguments in the paper, not computations.

Building the papers: `pdflatex` three times on each `.tex` file (no BibTeX needed).

## Motivation

We arrived at this question from the black-hole information problem. If evaporation is unitary the final radiation
is pure, and a Haar-typical pure state looks maximally mixed on every subsystem holding a fixed fraction $\alpha \lt  1/2$
of the qubits (Page). One may then ask at which order of correlations the information is written: not in any single
small subsystem, but in all $K$-body marginals *jointly*. The results themselves belong to quantum information theory.

## Use of AI

This work was carried out with extensive use of AI systems. The derivations, proofs, exact certificates,
verification code and the text of the paper were produced by AI agents (Anthropic Claude Opus models and OpenAI
Codex/GPT models) directed by the author, who chose the problem, organized the work and the cross-checks, and takes
responsibility for the manuscript. The proofs were checked by several independent AI readings from two different model
families, and the computer-assisted parts by exact-arithmetic verifiers. The Lean 4 formalization of the main
results was written by Claude agents (Anthropic) and is checked by the Lean kernel. **No human expert has yet
checked the proofs**; we would be grateful for any such check.

## Citation

```bibtex
@misc{tezgocen2026uda,
  author       = {Tezg{\"o}{\c{c}}en, Berke},
  title        = {Pure qubit states determined by marginals on fewer than half of the qubits:
                  a measure-one bound and a correction to the {Jones--Linden} lower bound},
  year         = {2026},
  howpublished = {\url{https://github.com/berketez/uda-fewer-than-half}}
}
```

## License

The paper (`paper/`) is licensed under [CC BY 4.0](https://creativecommons.org/licenses/by/4.0/). In
`verification/`, source code is under the MIT License and data and documentation are under CC BY 4.0
(see `verification/LICENSE`).

---

## Türkçe özet

**Saf qubit durumlarının qubitlerin yarısından azına ait marjinallerle belirlenmesi: ölçü-1 sınırı ve Jones–Linden
alt sınırının düzeltilmesi**

Çok qubitlik bir saf durumun ne kadarı küçük parçalarında yazılıdır? $n$ qubitlik saf bir durum, her $K$ qubitlik
alt kümedeki indirgenmiş durumları aynı olan başka hiçbir yoğunluk matrisi (saf ya da karışık) yoksa, $K$-cisim
marjinalleriyle *bütün durumlar arasında tek olarak belirlenir* (UDA). Jones ve Linden 2005'te, tarafların yarısından
azına ait marjinallerin hemen her durum için yetmediğini ileri sürdü. Bu alt sınır iddiası kuantum marjinal problemi
literatüründe hâlâ aktarılıyor.

Qubitler için tersinin doğru olduğunu gösteriyoruz. **Haar-hemen her $n$-qubit saf durum, $K(n) = 2\kappa_c n +
O(\log n) \approx 0{,}379\,n$ cisim marjinalleriyle UDA'dır.** Burada $\kappa_c \approx 0{,}189$, $h_2(\kappa) +
\kappa\log_2 3 = 1$ denkleminin köküdür. Açık eşikler: her $n \ge 139$ için qubitlerin yarısından azına ait
marjinaller, her $n \ge 996$ için $\lceil 0{,}4n \rceil$ cisim marjinalleri yeter. Böyle bir durum ayrıca pozitif yarı
tanımlı, $K(n)$-yerel bir Hamiltonyenin enerjisi sıfır olan tek temel durumudur.

Pozitif ölçülü eşik için $`K^{\ast}_{+}(n) = \kappa_c n + O(\log n)`$ gösteriyoruz; bu eşiğin baş katsayısı Linden–Wootters
(2002) parametre sayımının katsayısına eşittir. $(8,3)$, $(10,4)$ ve $(12,4)$ için nihai doğrulaması tam sayı ve
rasyonel eşitsizliklere dayanan açık UDA kümeleri veriyoruz. Sonuç olarak Jones–Linden alt sınırı qubitlerde her
$N \ge 7$ için yanlıştır; her $N \ge 139$ için tersi hemen her durumda doğrudur. Üst sınırları etkilenmez. Hatalı
adım, gerçel ikinci dereceden bir sistemde denklem sayımının gerçel bir çözüm ailesinin varlığına kanıt sayılmasıdır.

**Durum:** Teorem 1 (bütün eşikler ve asimptotik biçim), Lemma 1–3 ve Lemma A, Teorem 3'ün küçük vakaları
((4,2), (6,3), (8,3)) ve Teorem 2'nin üst sınırı Lean 4 ve Mathlib ile biçimsel olarak doğrulandı: `sorry` yok,
yalnız üç standart aksiyom var ve herkes `lean/` dizininde kendisi derleyebilir. Teorem 3'ün büyük
sertifikalarını, Teorem 2 (ii)'nin açık sınırını ve alt sınırları yalnızca yapay zekâ sistemleri ve kesin
aritmetikli doğrulayıcılar denetledi. İspatları henüz hiçbir insan uzman denetlemedi.

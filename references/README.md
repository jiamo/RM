# References

Papers and books consulted for the task board. PDFs we could download are under
`papers/` with extracted text under `txt/`; classics without a free download are
listed below with links, and the task board cites them by short name.

## Downloaded (arXiv PDFs in `papers/`, text in `txt/`)

| short name | paper | file | what it is used for |
|---|---|---|---|
| **BCY** | H. M. Bui, B. Conrey, M. P. Young, "More than 41% of the zeros of the zeta function are on the critical line", Acta Arith. 150 (2011) | `bcy-41percent.pdf` | the frontier: two-piece mollifier, κ ≥ 0.4105; the reduction to mean values (§2), the mean-value theorems (§3), the cross term (§5–6) |
| **PT** | D. J. Platt, T. Trudgian, "The Riemann hypothesis is true up to 3·10^12", Bull. LMS 53 (2021) | `platt-trudgian-verification.pdf` | numerical verification method: lattice sign-change counting of the completed zeta, Riemann–von Mangoldt count, interval arithmetic |
| **Sound** | K. Soundararajan, "Moments of the Riemann zeta-function", Ann. of Math. 170 (2009) | `soundararajan-moments.pdf` | the moment machinery: Selberg identity (Lemma 1), the moment conjecture, conditional results |
| **ZFR** | D. Johnston, A. Yang (eds., et al.), "Explicit zero-free regions for the Riemann zeta-function" | `zero-free-explicit.pdf` | explicit zero-free region σ > 1 − 1/(R log t), the ingredient list (§3–7) |
| **MT** | M. Mossinghoff, T. Trudgian, "Nonnegative trigonometric polynomials and a zero-free region for the Riemann zeta-function", Rocky Mountain J. Math. (2015) | `mossinghoff-trudgian-trigpoly.pdf` | the modern 3–4–1 trick: nonnegative trigonometric polynomials F40, the Euler-product combination, the region |
| **HN** | R. Prasad, M. Kumar, et al., "A note on Hardy's theorem" | `hardy-note.pdf` | Hardy's theorem: the first approximation formula, the two integration lemmas, the sign-change contradiction |
| **GL2** | N. Andersen, J. Thorner, "Zeros of GL₂ L-functions on the critical line" | `gl2-critical-line.pdf` | a modern exposition of the Levinson method: smooth mollified second moment (§2), reduction to shifted convolution sums (§3), approximate functional equation (Lemma 3.2) |

## Classics (no free PDF; metadata only)

| short name | reference | where to find it |
|---|---|---|
| **H14** | G. H. Hardy, "Sur les zéros de la fonction ζ(s) de Riemann", C. R. Acad. Sci. Paris 158 (1914), 1012–1014 | Gallica (gallica.bnf.fr); reproduced in Hardy's Collected Papers |
| **BL14** | H. Bohr, E. Landau, "Ein Satz über Dirichletsche Reihen mit Anwendung auf die ζ-Funktion und die L-Funktionen", Rend. Circ. Mat. Palermo 37 (1914), 269–272 | zbMATH 45.0343.01 |
| **dVp99** | C.-J. de la Vallée Poussin, "Sur la fonction ζ(s) de Riemann et le nombre des nombres premiers inférieurs à une limite donnée", Mém. Couronnés Acad. Belgique 59 (1899) | zbMATH 30.0198.02 |
| **S42** | A. Selberg, "On the zeros of Riemann's zeta-function", Skr. Norske Vid. Akad. Oslo I 10 (1942), 1–59 | Selberg, Collected Papers I |
| **Le74** | N. Levinson, "More than one third of zeros of Riemann's zeta-function are on σ = 1/2", Adv. Math. 13 (1974), 383–436 | zbMATH 0281.10017 |
| **C89** | J. B. Conrey, "More than two fifths of the zeros of the Riemann zeta function are on the critical line", J. reine angew. Math. 399 (1989), 1–26 | De Gruyter, open access |
| **Mo68** | H. L. Montgomery, "The analytic principle of the large sieve", Bull. Amer. Math. Soc. 74 (1968), 547–551 | AMS, open access |
| **In26** | A. E. Ingham, "Mean-value theorems in the theory of the Riemann zeta-function", Proc. London Math. Soc. 27 (1926), 273–300 | zbMATH 52.0338.03 |
| **HL18** | G. H. Hardy, J. E. Littlewood, "Contributions to the theory of the Riemann zeta-function...", Acta Math. 41 (1918), 119–196 | zbMATH 46.0498.01 |
| **Tit** | E. C. Titchmarsh, "The Theory of the Riemann Zeta-Function", 2nd ed., Oxford 1986 | archive.org (borrowable) |
| **Edw** | H. M. Edwards, "Riemann's Zeta Function", Academic Press 1974 | archive.org (borrowable) |
| **MV** | H. L. Montgomery, R. C. Vaughan, "Multiplicative Number Theory I", Cambridge 2007 | library |
| **Dav** | H. Davenport, "Multiplicative Number Theory", 3rd ed., Springer 2000 | library |
| **Ivi** | A. Ivić, "The Riemann Zeta-Function", 2nd ed., Dover 2003 | library |

## Physics, elliptic functions, and probability (added at the user's request)

The statistical (GUE) picture, the Hilbert-Polya spectral idea, the elliptic/modular
structure, and the probabilistic view are all *interpretive frameworks*; none has produced a
proof of RH.  Two adjacent results are real theorems worth formalizing:

- **Selberg's central limit theorem** (Selberg 1946; short proof by Radziwill-Soundararajan
  2017, arXiv:1708.04135): `log|zeta(1/2+it)|` over `t in [T, 2T]` is asymptotically normal
  with variance `1/2 log log T`.  Stated in `RiemannHypothesis/Partial.lean` as
  `SelbergCentralLimit`.
- **Rodgers-Tao 2018**, "The de Bruijn-Newman constant is non-negative" (Forum Math. Pi 8,
  2020, arXiv:1801.05914): `Lambda >= 0`; since RH is equivalent to `Lambda <= 0`, this
  rules out the naive Newman conjecture.  Requires defining the de Bruijn-Newman `H_t`
  family before it can be stated in Lean; recorded here as future work.

Conjectures stated in `RiemannHypothesis/Partial.lean`:
- `PairCorrelationConjecture` (Montgomery 1973, "The pair correlation of zeros of the zeta
  function", Proc. Sympos. Pure Math. 24, 181-193) with the GUE density
  `guePairCorrelationDensity`.
- `SelbergCentralLimit` (above).

## Claims that did not survive verification

- **Atiyah 2018** — M. Atiyah, "The Riemann Hypothesis" and "The Fine Structure
  Constant" (Heidelberg Laureate Forum, 24 Sep 2018): a claimed proof of RH via a
  "Todd function" and the fine-structure constant, depending on a weak form of the
  Lehmer conjecture. Not accepted: the Todd function was not rigorously defined, the
  argument did not withstand scrutiny, and no verification exists. Recorded here as the
  canonical example of why this project's claim-hygiene rule exists: a claim is not a
  result until verified. Not a partial result, not a task, not a route.

## Methodology reference (agent-driven proof discovery)

- **Crouzeix-conjecture agent conversation** (2026-07): a Codex multi-agent attempt at
  Crouzeix's conjecture (the numerical range is a 2-spectral set). The conversation is
  instructive for its *workflow*, not its mathematics: several independent proof families
  (analytic/dilation, extremal geometry, operator-algebraic) plus an adversarial audit
  track that re-checks every claimed constant and hidden assumption and rejects status
  reports; the only surviving piece was an abstract completion lemma in the operator-valued
  Herglotz positive-kernel framework. Two transfers to this board: the adversarial-audit
  gate (`M0-ADVERSARIAL-AUDIT`) and the observation that the Herglotz method is the same
  analytic family as Weil's positivity criterion for RH (`M2-WEIL-POSITIVITY`).

## Reading notes (what the board's fine tasks are based on)

- **Zero-free region** (M1-ZFR-*): the classical argument is the 3–4–1 inequality
  `3 + 4 cos θ + cos 2θ = 2(1 + cos θ)² ≥ 0` inserted into the Euler product, giving
  `|ζ(σ)³ ζ(σ+it)⁴ ζ(σ+2it)| ≥ 1` for σ > 1, combined with the growth bound
  `|ζ(σ+it)| ≪ log t / (σ − 1)` for 1 < σ ≤ 2 (Euler–Maclaurin / partial summation).
  MT generalize the 3–4–1 polynomial to longer nonnegative trigonometric polynomials;
  ZFR make the constant explicit (σ > 1 − 1/(R log t), |t| ≥ 3, R ≈ 5.57).
- **Hardy's theorem** (M1-HARDY-*): the real function on the critical line, the first
  approximation formula `ζ(s) = Σ_{n≤x} n^{-s} + χ(s) Σ_{n≤x} n^{s−1} + O(·)`, and the
  sign-change argument (HN §2–3).
- **Mean values** (M1-MV-*): the second moment `∫₀^T |ζ(1/2+it)|² dt ~ T log T`
  (HL18), the fourth moment `~ T log⁴T/(2π²)` (In26), the Dirichlet-polynomial mean value
  theorem (MV ch. 7), via the approximate functional equation.
- **Levinson method / critical line** (M2-*): the reduction `κ ≥ 1 − (1/R) log((1/T)∫|Vψ|²)`
  from Littlewood's lemma + AM–GM (BCY §2); the mollified second moment (GL2 §2); the
  shifted convolution sums (GL2 §3); the two-piece mollifier cross term (BCY §5–6);
  history S42 → Le74 → C89 → BCY.
- **Numerical verification** (M1-VERIFY): evaluate the completed zeta on a lattice of
  spacing ~0.01 on the critical line, count sign changes, compare with the
  Riemann–von Mangoldt expected count (PT).

The papers in `papers/` are the primary sources for the exit criteria and lemma
structure of the corresponding tasks; the classics are cited by name where the modern
expositions (BCY, GL2, HN, MT) reproduce or extend them.

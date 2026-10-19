# The approximate functional equation on the critical line, proved: `AFECriticalLine 250`

Date: 2026-10-19
Tasks: `M1-AFE-CRITICAL-LINE` (new, `DONE_STRONG`; R2 and R3 of round 5), `M1-ZETA-CHI-AFE`
(`DONE_WEAK` → `DONE_STRONG`), `M1-VDC-B-PROCESS` (new, `TODO_READY`; R1 of round 5, not proved)
Modules (all new): `RiemannHypothesis/OscillatoryIntegral.lean`,
`RiemannHypothesis/PoissonSummationInterval.lean`, `RiemannHypothesis/LaplaceGamma.lean`,
`RiemannHypothesis/ZetaMellinPhase.lean`, `RiemannHypothesis/ZetaStationaryPhase.lean`,
`RiemannHypothesis/AFEIntegrals.lean`, `RiemannHypothesis/AFEProof.lean`,
`RiemannHypothesis/AFECriticalLineProof.lean`.
Mode: a **proof** in this repository; nothing is assumed.

## Claim

`AFECriticalLine` (in `RiemannHypothesis/ApproximateFunctionalEquation.lean`) is unchanged:

```lean
def AFECriticalLine (C : ℝ) : Prop :=
  ∀ t : ℝ, 2 ≤ t →
    ‖riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)
        - zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I)‖
      ≤ C * t ^ (-(1 / 4) : ℝ)
```

with `afeLength t = ⌊√(t/2π)⌋`.  The new theorems, verbatim (proofs omitted):

```lean
-- RiemannHypothesis/PoissonSummationInterval.lean
theorem hasSum_sum_Ioc_halfInt {A B : ℕ} (hAB : A ≤ B) {G G' G'' : ℝ → ℂ}
    (hG : ∀ x ∈ Icc ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2), HasDerivAt G (G' x) x)
    (hG' : ∀ x ∈ Icc ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2), HasDerivAt G' (G'' x) x)
    (hG''c : ContinuousOn G'' (Icc ((A : ℝ) + 1 / 2) ((B : ℝ) + 1 / 2))) :
    HasSum (fun n : ℕ => 2 * ∫ x in ((A : ℝ) + 1 / 2)..((B : ℝ) + 1 / 2),
        G x * (Real.cos (2 * Real.pi * ((n + 1 : ℕ) : ℝ) * x) : ℂ))
      (∑ k ∈ Finset.Ioc A B, G k - ∫ x in ((A : ℝ) + 1 / 2)..((B : ℝ) + 1 / 2), G x) :=

-- RiemannHypothesis/LaplaceGamma.lean
theorem integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos {a r : ℂ} (ha : 0 < a.re) (hr : 0 < r.re) :
    ∫ u in Ioi (0 : ℝ), (u : ℂ) ^ (a - 1) * cexp (-(r * u)) = (1 / r) ^ a * Gamma a :=

-- RiemannHypothesis/ZetaMellinPhase.lean
theorem tendsto_integral_mellin {t ω : ℝ} (ht : 0 ≤ t) (hω : 0 < ω) :
    Tendsto (fun B => ∫ u in (0 : ℝ)..B, ((1 / Real.sqrt u : ℝ) : ℂ) * expI (phase t ω) u) atTop
      (𝓝 (mellinMain t ω)) :=

-- RiemannHypothesis/ZetaMellinPhase.lean
theorem norm_mellinMain_sub_zetaChi_le (t : ℝ) {ν : ℝ} (hν : 0 < ν) :
    ‖mellinMain t (2 * Real.pi * ν) - zetaChi (1 / 2 + (t : ℂ) * I) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)‖
      ≤ ν ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * t)) :=

-- RiemannHypothesis/ZetaStationaryPhase.lean
theorem norm_integral_sub_zetaChi_add_boundary_le {t ν a b : ℝ} (ht : 0 < t) (hν : 0 < ν)
    (ha : 0 < a) (hat : 2 * Real.pi * ν * a < t) (hbt : t < 2 * Real.pi * ν * b) :
    ‖mI t (2 * Real.pi * ν) a b - zetaChi (1 / 2 + (t : ℂ) * I) * (ν : ℂ) ^ ((1 / 2 + (t : ℂ) * I) - 1)
        + I * (bdry t (2 * Real.pi * ν) b - bdry t (2 * Real.pi * ν) a)‖
      ≤ 2 * (|ampK t (2 * Real.pi * ν) a| + |ampK t (2 * Real.pi * ν) b|)
        + ν ^ (-(1 / 2 : ℝ)) * Real.exp (-(Real.pi * t)) :=

-- RiemannHypothesis/AFECriticalLineProof.lean
theorem norm_afe_error_le_large {t : ℝ} (ht : 200 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)
        - zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I)‖
      ≤ 80 / Real.sqrt ((afeLength t : ℝ) + 1 / 2) :=

-- RiemannHypothesis/AFECriticalLineProof.lean
theorem eighty_div_sqrt_le {t : ℝ} (ht : 0 < t) :
    80 / Real.sqrt ((afeLength t : ℝ) + 1 / 2) ≤ 200 * t ^ (-(1 / 4) : ℝ) :=

-- RiemannHypothesis/AFECriticalLineProof.lean
theorem norm_afe_error_le_small {t : ℝ} (ht : 2 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I) - zetaSum (afeLength t) (1 / 2 + (t : ℂ) * I)
        - zetaChi (1 / 2 + (t : ℂ) * I) * zetaSumDual (afeLength t) (1 / 2 + (t : ℂ) * I)‖
      ≤ 2 * Real.sqrt t + 13 + 4 * t ^ ((1 : ℝ) / 4) :=

-- RiemannHypothesis/AFECriticalLineProof.lean
theorem afeCriticalLine : AFECriticalLine 250 :=

-- RiemannHypothesis/AFECriticalLineProof.lean
theorem norm_riemannZeta_criticalLine_le {t : ℝ} (ht : 2 ≤ t) :
    ‖riemannZeta (1 / 2 + (t : ℂ) * I)‖ ≤ (250 + 4) * t ^ ((1 : ℝ) / 4) :=
```

Namespaces: `RiemannHypothesis.PoissonInterval`, `RiemannHypothesis.LaplaceGamma`,
`RiemannHypothesis.ZetaMellinPhase` (for `ZetaMellinPhase.lean` and `ZetaStationaryPhase.lean`),
`RiemannHypothesis.AFEProof` (for `norm_afe_error_le_large`, `eighty_div_sqrt_le`,
`norm_afe_error_le_small`), and `RiemannHypothesis` (for `afeCriticalLine` and
`norm_riemannZeta_criticalLine_le`).

## The route

1. **Exact Poisson summation between half-integers** (`PoissonSummationInterval.lean`).  The
   first-order Euler–Maclaurin formula with the sawtooth `ψ(x) = {x} − 1/2`, and one integration by
   parts against the periodic Bernoulli function `P₂(x) = B₂({x})/2 = ∑_{n≥1} cos(2πnx)/(2π²n²)`
   (Mathlib's Fourier series of the Bernoulli polynomials), give for `0 ≤ a ≤ b` and `G` of class
   `C²` the convergent series `∑_{a<n≤b} G(n) = ∫_a^b G + ψ(a)G(a) − ψ(b)G(b) + ∑_{n≥1} S_n`
   (`hasSum_sum_Ioc_sub_integral`).  At `a = A + 1/2`, `b = B + 1/2` the boundary terms vanish:
   `∑_{A<n≤B} G(n) − ∫_a^b G = ∑_{ν≥1} 2∫_a^b G(x) cos(2πνx) dx` (`hasSum_sum_Ioc_halfInt`).
   No truncation in `ν` is made, so the general truncated formula (Lemma 4.10) is not needed.
2. **The Mellin phase** (`LaplaceGamma.lean`, `ZetaMellinPhase.lean`).  For `s = 1/2 + it`,
   `ν > 0`: `∫_0^B u^(−s) e^{iωu} du → Γ(1−s)(i/ω)^(1−s)` (`tendsto_integral_mellin`).  Mathlib has
   `∫_0^∞ u^(a−1) e^(−ru) du = r^(−a)Γ(a)` for real `r > 0`; `LaplaceGamma.lean` extends it to
   `re r > 0` by analytic continuation, and `ZetaMellinPhase.lean` lets `r = ε − iω`, `ε → 0⁺`,
   with the tails bounded uniformly in `ε` by the first-derivative test.  **This replaces the
   Fresnel integral: neither a contour rotation nor `∫ e(u²)` is used; the limit is taken in the
   damping of the Laplace transform.**  With `ω = 2πν`, since
   `χ(s) = 2(2π)^(s−1)Γ(1−s) sin(πs/2)` by definition, writing `i^(1−s) = e^{iπ(1−s)/2}` and
   `sin` through exponentials gives `Γ(1−s)(i/2πν)^(1−s) = χ(s) ν^(s−1) + E` with an explicit `E`
   (`mellinMain_sub_zetaChi_eq`), `‖E‖ ≤ ν^(−1/2) e^(−πt)` (`norm_mellinMain_sub_zetaChi_le`); no
   Stirling formula.
3. **Stationary phase** (`OscillatoryIntegral.lean`, `ZetaStationaryPhase.lean`,
   `AFEIntegrals.lean`).  Exact second-order integration by parts with `h = √u/(ωu − t)` and
   `k = h'/Φ'`, `Φ(u) = ωu − t log u`, on `[0, a]` and `[b, ∞)` and subtraction from the complete
   integral give, for `0 < a < t/(2πν) < b`,
   `‖∫_a^b u^(−1/2) e^{iΦ} − χ(s)ν^(s−1) + i[h e^{iΦ}]_a^b‖ ≤ 2(|k(a)| + |k(b)|) + ν^(−1/2)e^(−πt)`
   (`norm_integral_sub_zetaChi_add_boundary_le`).  The reflected frequency `−2πν` has no
   stationary point (`norm_mI_neg_add_boundary_le`); near the stationary point the
   second-derivative test gives `‖I(a, b)‖ ≤ 24√a/√t + 2h(2a)` (`norm_mI_le_of_near`).
4. **Frequency ranges** (`AFEProof.lean`).  `N = ⌊√(t/2π)⌋`, `a = N + 1/2`, `B = ⌈t⌉²`,
   `b = B + 1/2`, `c = t/(2πa)` (so `N − 1 ≤ c ≤ N + 2`).  Theorem 4.11 at `x = b`
   (`M1-ZETA-PARTIAL-SUM`) gives
   `‖ζ(s) − ∑_{n≤N} n^(−s) − X‖ ≤ 11 b^(−1/2) + √a/t + ‖∑_ν F_ν − X‖`
   (`norm_zeta_sub_zetaSum_sub_le`), `F_ν` the `ν`-th Poisson integral of `n^(−s)` on `(a, b]`
   (`hasSum_Fν`).  Lower range `1 ≤ ν ≤ c − 1`: main term `χ(s)ν^(s−1)`, endpoint terms at `a`
   with sign `(−1)^ν` summed as an alternating series (`norm_sum_lower_le`); near range, at most
   four `ν` (`norm_Fν_le_remR`) plus the at most two main terms between `c − 1` and `N`
   (`zetaSumDual_split`); upper range `ν ≥ c + 1`, no stationary point, alternating endpoint
   terms (`norm_sum_upper_le`).  Together: `norm_poisson_sub_main_le`.
5. **Numerical bookkeeping** (`afe_bound_numeric`, `num_T1` … `num_T8`): for `N ≥ 5`,
   `4a² ≤ t`, `c ≤ 2a`, `t ≤ √b`, the sum of all error terms is `≤ 80/√a`.

## The constants

* `t ≥ 200` (so `N ≥ 5`): error `≤ 80/√(N + 1/2)` (`norm_afe_error_le_large`).
* `80/√(N + 1/2) ≤ 200 t^(−1/4)` for every `t > 0` (`eighty_div_sqrt_le`).
* `2 ≤ t ≤ 200`: error `≤ 2√t + 13 + 4t^(1/4)` (`norm_afe_error_le_small`: Theorem 4.11 at
  `x = t` gives `‖ζ(1/2+it)‖ ≤ 2√t + 13`, and the two sums are bounded trivially by `2√N`), and
  `(2√t + 13 + 4t^(1/4)) t^(1/4) ≤ 250` on `[2, 200]`.
* Hence `C₀ = 250`: `afeCriticalLine : AFECriticalLine 250`.
* Corollary, from the unchanged `norm_riemannZeta_criticalLine_le_of_afe`:
  `‖ζ(1/2 + it)‖ ≤ (250 + 4) t^(1/4) = 254 t^(1/4)` for `t ≥ 2`
  (`norm_riemannZeta_criticalLine_le`).

The constants are not optimized.

## Axioms

`#print axioms` for the new theorems (the nineteen lines added to step 3 of `scripts/audit.sh`,
run with `lake env lean` on a file importing `RiemannHypothesis.AFECriticalLineProof`; the same
lines appear in the output of `bash scripts/audit.sh`):

```text
'RiemannHypothesis.Oscillatory.integral_eq_second_order' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.Oscillatory.norm_integral_add_boundary_le_of_monotone' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RiemannHypothesis.PoissonInterval.hasSum_sum_Ioc_sub_integral' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RiemannHypothesis.PoissonInterval.hasSum_sum_Ioc_halfInt' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.LaplaceGamma.integral_cpow_mul_exp_neg_mul_Ioi_of_re_pos' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RiemannHypothesis.ZetaMellinPhase.tendsto_integral_mellin' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.ZetaMellinPhase.norm_mellinMain_sub_zetaChi_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RiemannHypothesis.ZetaMellinPhase.norm_integral_sub_mellinMain_add_boundary_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RiemannHypothesis.ZetaMellinPhase.norm_integral_sub_zetaChi_add_boundary_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RiemannHypothesis.ZetaMellinPhase.norm_mI_neg_add_boundary_le' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
'RiemannHypothesis.ZetaMellinPhase.norm_mI_le_of_near' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.AFEProof.hasSum_Fν' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.AFEProof.norm_zeta_sub_zetaSum_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.AFEProof.norm_poisson_sub_main_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.AFEProof.afe_bound_numeric' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.AFEProof.norm_afe_error_le_large' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.AFEProof.norm_afe_error_le_small' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.afeCriticalLine' depends on axioms: [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.norm_riemannZeta_criticalLine_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Conditional theorems

`AFECriticalLine` was the hypothesis of the two theorems `norm_riemannZeta_criticalLine_le_of_afe`
(namespaces `RiemannHypothesis` and `RiemannHypothesis.AFESubconvexity`).  Both statements are
unchanged; since `afeCriticalLine` now proves `AFECriticalLine 250`,
`scripts/conditional_theorems.lean` (step 2: a hypothesis `AFECriticalLine C` with `C` bound is
discharged when the head constant is proved somewhere) no longer reports them.  The output of
`lake env lean scripts/conditional_theorems.lean` changed, and
`docs/goal/conditional-theorems.txt` is regenerated in the same commit:

```diff
--- docs/goal/conditional-theorems.txt (before)
+++ docs/goal/conditional-theorems.txt (after)
@@ -1,6 +1,5 @@
 # UNCLASSIFIED: unproved statements missing from the classification in scripts/conditional_theorems.lean
 # OPEN: theorems conditional on a statement this repository cannot prove
-  RiemannHypothesis.AFESubconvexity.norm_riemannZeta_criticalLine_le_of_afe <- RiemannHypothesis.AFECriticalLine
   RiemannHypothesis.chebyshevAbel_eq <- RiemannHypothesis.ChebyshevBoundForm
   RiemannHypothesis.differentiableOn_chebyshevAbel <- RiemannHypothesis.ChebyshevBoundForm
   RiemannHypothesis.differentiableOn_liouvilleAbel <- RiemannHypothesis.LiouvilleBoundForm
@@ -14,7 +13,6 @@
   RiemannHypothesis.liouvilleAbel_eq <- RiemannHypothesis.LiouvilleBoundForm
   RiemannHypothesis.mertensBound_of_redhefferBound <- RiemannHypothesis.RedhefferBoundForm
   RiemannHypothesis.moebiusAbel_eq_LSeries <- RiemannHypothesis.MertensBoundForm
-  RiemannHypothesis.norm_riemannZeta_criticalLine_le_of_afe <- RiemannHypothesis.AFECriticalLine
   RiemannHypothesis.norm_riemannZeta_le_exp_of_zetaStripForm <- RiemannHypothesis.ZetaStripForm
   RiemannHypothesis.one_fifth_off_critical_line_of_eightyPercent <- RiemannHypothesis.EightyPercentOnCriticalLine
   RiemannHypothesis.partialSumBound_moebiusOverN <- RiemannHypothesis.LittleMertensBoundForm
```

`AFECriticalLine` is also removed from the `openStatements` classification list of that script
(it no longer affects the output).

## What is not proved

* **R1, the general truncated Poisson summation** (Titchmarsh, Lemma 4.10) for arbitrary real
  endpoints, with error `O_η(log(β − α + 2))`, and its weighted forms.  R3 did not need it: at
  half-integer endpoints the exact formula has no boundary terms and no truncation is made.  An
  uncommitted attempt, `RiemannHypothesis/PoissonTruncated.lean`, did not build and did not state
  the main theorem; it was deleted.  Open as `M1-VDC-B-PROCESS` (`TODO_READY`, head of the queue).
* The general Theorem 4.12/4.13 form (`σ ≠ 1/2`, `2πxy = t`), and the Riemann–Siegel formula.
* Moments: the fourth moment still needs the mean value theorem applied to the square of the
  approximate functional equation, and the divisor sums (`M2-MEANVALUE`, item (ii)).

## Commands and gates

```text
$ lake build RiemannHypothesis.AFECriticalLineProof        (focused; all eight modules built)
⚠ [8732/8732] Built RiemannHypothesis.AFECriticalLineProof (20s)
$ lake build
✔ [12528/12529] Built RiemannHypothesis (9.1s)
Build completed successfully (12529 jobs).
$ lake env lean scripts/conditional_theorems.lean > docs/goal/conditional-theorems.txt
(output changed: the two lines shown in the diff above are removed)
$ bash scripts/audit.sh
==> exhaustive axiom audit (scripts/axiom_audit.lean)
AXIOM AUDIT: 32371 theorems checked, 0 outside the standard three
OK
==> coverage of the pinned axiom checks (scripts/audit_coverage.py)
exported theorems : 28938
audited names     : 912
covered           : 912 (3.2%)
missing coverage  : 28026
stale audit lines : 0
==> checking for Float
==> pinning the claims of the closed rows (scripts/revalidation.lean)
==> checking the conditional/unconditional boundary
==> validating the task board
OK: 189 tasks validate
OK
(exit status 0)
$ python3 scripts/goal_state.py validate
OK: 189 tasks validate
```

## Adversarial revalidation: M1-AFE-CRITICAL-LINE

* *Statement.*  `afeCriticalLine` is pinned in `scripts/revalidation.lean` twice: as
  `AFECriticalLine 250`, and with the definition written out (`afeLength` unfolded to
  `⌊Real.sqrt (t / (2 * Real.pi))⌋₊`).  The existing pin of `AFECriticalLine C` by `rfl` (row
  `M1-ZETA-CHI-AFE`) shows the definition is the one recorded in round 1, unchanged.
* *Constants, by hand.*  For `t ≥ 200`, `x = √(t/2π) ≥ 5.64`, `N + 1/2 ≥ x − 1/2 ≥ 0.91x`, so
  `80/√(N + 1/2) ≤ 83.8 x^(−1/2) = 83.8 (2π)^(1/4) t^(−1/4) ≤ 133 t^(−1/4) ≤ 200 t^(−1/4)`.  At
  `t = 200`: `2√200 + 13 + 4·200^(1/4) = 28.3 + 13 + 15.0 = 56.3` and `56.3 · 200^(1/4) = 211.8
  ≤ 250`; at `t = 2`: `(2.83 + 13 + 4.76)·1.19 = 24.4 ≤ 250`; the function is increasing in `t`.
  `250 + 4 = 254`.
* *Main term.*  `norm_mellinMain_sub_zetaChi_le` is the place where `χ` enters; it is pinned
  with `mellinMain` unfolded to `Γ(1 − s)(i/(2πν))^(1−s)`, so the main term is not a renamed
  `χ`.  `‖χ(1/2+it)‖ = 1` is used only through the unchanged `norm_zetaChi_criticalLine`.
* *Hypotheses.*  `t ≥ 2` is part of `AFECriticalLine` itself.  The large-`t` theorem needs
  `t ≥ 200` only to get `N ≥ 5`; it is not vacuous (`afeLength 200 = 5`).
* *No hidden assumption.*  The exhaustive axiom audit (step 3b of `scripts/audit.sh`) covers
  every theorem of the eight modules; the pinned list (step 3) names nineteen of them.  No `def …
  : Prop` is added; no `sorry`, `native_decide` or `axiom` occurs in the modules.
* *Claim mode.*  Proved here; the only Mathlib inputs named are the real-frequency Laplace
  transform of `u^(a−1)` and the Fourier series of the Bernoulli polynomials.

## Adversarial revalidation: M1-ZETA-CHI-AFE

* The row's exit criteria are pinned since round 1 (`sum_one_div_sqrt_le`,
  `riemannZeta_eq_zetaChi_mul`, `norm_zetaChi_criticalLine`, `zetaSumDual_criticalLine`,
  `norm_zetaSum_criticalLine_le`, `AFECriticalLine` by `rfl`, and
  `norm_riemannZeta_criticalLine_le_of_afe`); none of these statements changed in this round.
* Its open boundary was exactly that `AFECriticalLine` was not proved.  That is now
  `afeCriticalLine` (row `M1-AFE-CRITICAL-LINE`), pinned above.  The rest of the old boundary
  text was scope (only the trivial bound for the two polynomials; no moment or density
  consequence); it is kept in the row's `latest_update` and in its last exit criterion.
* The conditional bound `(C + 4) t^(1/4)` is checked at `C = 250` by the pin of
  `norm_riemannZeta_criticalLine_le`.

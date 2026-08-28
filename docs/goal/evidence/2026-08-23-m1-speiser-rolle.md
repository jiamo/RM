# M1-SPEISER-ROLLE — Rolle on the critical line, and the price of the Speiser transfer

Date: 2026-08-23
Modules: `RiemannHypothesis/EightyPercentMultiplicity.lean`, `RiemannHypothesis/CriticalLineXi.lean`,
`RiemannHypothesis/SpeiserRolle.lean`, `RiemannHypothesis/SpeiserEquivalence.lean`
(all imported by `RiemannHypothesis.lean`)

## What is proved

Unconditional:

* `onLine`, `XiReal` — the parametrisation `t ↦ 1/2 + it` of the critical line and Hardy's real
  function `Ξ(t) = ξ(1/2 + it)`.  `xiFn_onLine_conj` and `xiFn_onLine_im` prove that `ξ` is real
  there, from `ξ(conj s) = conj ξ(s)` and the functional equation.
* `hasDerivAt_XiReal` — `Ξ` is differentiable with `Ξ′(t) = Re(i·ξ′(1/2 + it))`, and
  `xiDerivFn_onLine_mul_I_im` shows the imaginary part of `i·ξ′(1/2 + it)` vanishes, so
  `xiDerivFn_onLine_eq_zero_of_deriv_eq_zero`: a critical point of `Ξ` is a genuine zero of `ξ′`.
* `exists_xiDerivFn_onLine_eq_zero` — **Rolle's theorem on the critical line**: between two zeroes
  of `ξ` on the line there is a zero of `ξ′` on the line.
* `windowCountOffLineMult_add_windowCountOnLineMult` — the window count of the zeroes of `ζ`
  splits, *with multiplicity*, into its off-line and on-line parts; `windowCountOffLineMult_eq`
  identifies the off-line part as the distinct count plus the excess multiplicity.  The same
  split for `ξ′` is `xiDerivWindowCountOffLineMult_add_onLineMult`.
* `windowCountOnLineMult_le_xiDerivWindowCountOnLineMult` — **`N₀ᵐ(T₁,T₂) ≤ N₀ᵐ_{ξ′}(T₁,T₂) + 1`**.
  Counted with multiplicity, `ξ′` has at least as many zeroes on the critical line as `ζ` has, up
  to one.  The proof combines Rolle (one gap zero strictly between each pair of consecutive
  on-line ordinates, `card_le_card_add_one_of_gap`) with the local fact `m_{ξ′}(ρ) = m_ζ(ρ) − 1`
  at a zero of `ζ` (M1-SPEISER-MULTIPLE), the two contributions being disjoint.
* `xiDerivWindowCountOffLineMult_le_windowCountOffLineMult` — equivalently, and again
  unconditionally, `ξ′` has at most as many *off-line* zeroes as `ζ`, up to `O(log T)`; this uses
  the Riemann–von Mangoldt comparison of `N` and `N_{ξ′}`.

Conditional, and what fixes the price of the hypothesis:

* `SpeiserOffLineTransfer` and `XiDerivOnLineDominates`, the off-line and on-line forms of the
  transfer with multiplicity, are proved **equivalent**
  (`speiserOffLineTransfer_iff_xiDerivOnLineDominates`).
* `eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer` — under the hypothesis, at
  least `86.864 %` of the zeroes of `ζ`, counted with multiplicity, lie on the critical line;
  hence `eightyPercentOnCriticalLineMult_of_speiserOffLineTransfer`.
* `SpeiserTransferMult` and the chain
  `speiserTransfer_of_speiserTransferMult`, `offLineMult_le_of_speiserTransferMult`,
  `eighty_six_percent_on_critical_line_mult_of_speiserTransferMult`, together with the weaker
  `seventy_three_percent_on_critical_line_mult_of_speiserTransfer` obtained from the distinct-point
  hypothesis alone.

## Consequence for M1-EIGHTY-CRITICAL-ROUTE

The hypothesis of that row is therefore *not* an auxiliary input on the way to `80 %`: with
multiplicity it is equivalent to the reverse of an inequality whose easy half is exactly what
Rolle's theorem gives, and it already implies `86.864 %` on the critical line — more than the
target it was introduced to reach.  It is also not the Levinson–Montgomery theorem, which counts
zeroes of `ζ′`, not of `ξ′`.  The docstrings of `RiemannHypothesis/EightyPercentRoute.lean` and
the README have been corrected; the row's status and its conditional consequences are unchanged.

## Scope — what is *not* claimed

* Neither `SpeiserOffLineTransfer` nor `XiDerivOnLineDominates` is proved.  Only the reverse
  direction is, and it is the elementary one.
* The unconditional proportion of zeroes of `ζ` known to lie on the critical line is unchanged:
  `2/3`, and `0.6725…` with the optimal window.
* Nothing here bears on the Riemann Hypothesis.

## Gates

* `lake build` — succeeds; in particular
  `lake build RiemannHypothesis.CriticalLineXi RiemannHypothesis.SpeiserRolle
  RiemannHypothesis.SpeiserEquivalence RiemannHypothesis.EightyPercentMultiplicity`.
* No `sorry` in any of the four modules.
* `lake env lean scripts/revalidation.lean` — elaborates; the statements above are pinned there.
* Axioms: exactly `propext`, `Classical.choice`, `Quot.sound`.

## Adversarial revalidation: M1-SPEISER-ROLLE

A second pass, made against the compiled modules rather than against this note.

* **Is `windowCountOnLineMult_le_xiDerivWindowCountOnLineMult` vacuous?**  No.  It is an
  inequality between finite sums that are known to be nonzero for large windows: Hardy's theorem
  (M1-CRITICAL-LINE-ORDINATES) gives on-line zeroes of arbitrarily large ordinate, so the left
  side is positive for suitable `T₁ < T₂`, and the bound then forces `ξ′` to have on-line zeroes
  too.  The `+ 1` is genuinely needed and not a way of making the statement trivial: it accounts
  for the single missing gap below the first on-line zero of the window.
* **Is the counting double-counted?**  `sum_multiple_add_gap_le` adds two contributions to
  `xiDerivWindowCountOnLineMult`: the multiplicities `m_ζ(ρ) − 1` carried at the on-line zeroes of
  `ζ`, and the gap zeroes, which are by definition (`xiDerivWindowGapZeros`) *not* zeroes of `ζ`.
  The two index sets are disjoint, and the disjointness is proved, not assumed.
* **Does Rolle apply?**  `exists_hasDerivAt_eq_zero` needs continuity on `[a,b]`, equality of the
  endpoint values, and differentiability on the interior; all three come from `hasDerivAt_XiReal`,
  which is proved for *every* real `t`, and from `XiReal_eq_zero_iff`.  The passage back from
  `Ξ′(t) = 0` to `ξ′(1/2 + it) = 0` is not a slip: it needs `xiDerivFn_onLine_mul_I_im`, the
  vanishing of the imaginary part, which is proved separately from the reality of `ξ` on the line.
* **Is the equivalence an artefact?**  No.  `speiserOffLineTransfer_iff_xiDerivOnLineDominates`
  uses only the two splittings and `abs_xiDerivWindowCount_sub_windowCount_le`, itself proved from
  the two Riemann–von Mangoldt formulas.  Both directions are proved; neither is `Iff.rfl`.
* **Does anything here prove the hypothesis?**  No.  `SpeiserOffLineTransfer` is a `def … : Prop`
  with no term of that type anywhere in the repository; the `86.864 %` theorem takes it as an
  explicit argument.
* **Proof hygiene.**  No `sorry`, `axiom`, `native_decide` or `implemented_by` in the four
  modules; `#print axioms` on each named theorem returns exactly `propext`, `Classical.choice`,
  `Quot.sound`.
* **Duplication check.**  `xiDerivMultiplicity` and `m_{ξ′}(ρ) + 1 = m_ζ(ρ)` are reused from
  `RiemannHypothesis/SpeiserMultiple.lean`, not redeclared; the window counting vocabulary is
  reused from `RiemannHypothesis/EightyPercent.lean`.

# M1-SUBCONVEXITY-LEFT and M1-GROWTH — subconvexity on `σ ≤ 1/2`, and the convexity bound with no logarithm

Files: `RiemannHypothesis/SubconvexityLeft.lean`, `RiemannHypothesis/ConvexityLogFree.lean`.
Gates: `lake build RiemannHypothesis.SubconvexityLeft`,
`lake build RiemannHypothesis.ConvexityLogFree`, `./scripts/audit.sh`.

## What is proved

1. **The Weyl exponent at every height** (`exists_bound_criticalLine_sixth`): there is `A > 0`
   with

   ```
   ‖ζ(1/2 + i t)‖ ≤ A · |t|^(1/6) · (1 + log|t|)   for all |t| ≥ 3.
   ```

   `M1-SUBCONVEXITY-UNCONDITIONAL` proves this for `t ≥ 10⁹` only, and only for positive `t`.
   Below the threshold the convexity bound `C (1 + log|t|) |t|^(1/4)` is smaller than
   `6 C (1+log|t|) |t|^(1/6)` because `|t|^(1/12) ≤ (10⁹)^(1/12) ≤ 6`; for negative `t` the
   conjugation symmetry `ζ(conj s) = conj ζ(s)` (`riemannZeta_conj_of_mem_strip`) gives
   `‖ζ(1/2 - i t)‖ = ‖ζ(1/2 + i t)‖` (`norm_riemannZeta_criticalLine_abs`).

2. **Subconvexity on the left of the critical line**
   (`norm_riemannZeta_le_subconvexity_left`): there is `C > 0` with

   ```
   ‖ζ(σ + i t)‖ ≤ C (1 + log|t|) |t|^(1/2 - 2σ/3)   for 0 ≤ σ ≤ 1/2, |t| ≥ 3.
   ```

   Before this row, nothing better than convexity was proved for `σ ≤ 1/2`.

3. **The logarithm-free convexity bound** (`norm_riemannZeta_le_convexity_logfree`), the first
   exit criterion of `M1-GROWTH`: for every fixed `σ` with `0 < σ < 1` there is `C > 0` with

   ```
   ‖ζ(σ + i t)‖ ≤ C |t|^((1-σ)/2)   for all |t| ≥ 3,
   ```

   with no `ε` and no logarithm.

   The same statement is also recorded in asymptotic form,
   `isBigO_riemannZeta_convexity_logfree : (fun t => ζ(σ + i t)) =O[atTop] fun t => t^((1-σ)/2)`.

4. **The zero-free-region shape** (`norm_riemannZeta_le_log_div_of_one_lt_re`), the second exit
   criterion of `M1-GROWTH`: `‖ζ(σ + i t)‖ ≤ 2 log|t| / (σ - 1)` for `1 < σ ≤ 2`, `|t| ≥ 3`.

## The argument

**Interpolation on `0 ≤ σ ≤ 1/2`.**  Phragmén–Lindelöf is applied, exactly as in
`RiemannHypothesis/Convexity.lean` and `RiemannHypothesis/ConvexityLog.lean`, to

```
g(s) = ζ(s) · u(s)^(-w(s)) / log u(s),   u(s) = s(1-s) + 4,   w(s) = 1/4 - s/3,
```

on the strip `0 < re s < 1/2` (width `1/2`, so the growth hypothesis needs `c < 2π`, and `ζ`
is at most `100 e^(π|t|/2)|t|²` there).  No rational factor is needed: `ζ` has no pole in the
closed strip `0 ≤ σ ≤ 1/2`.  On the closed strip `re u ≥ t² + 4`, so

* `‖u^(-w)‖ = exp(-(1/4 - σ/3) log‖u‖ - (t/3) arg u)` lies between `e^(-π/6)/2 · |t|^(-(1/2-2σ/3))`
  and `e^(π/6) · |t|^(-(1/2-2σ/3))` (`norm_expLeft_ge`, `norm_expLeft_le`), because
  `t² ≤ ‖u‖ ≤ 2t²` and `|arg u| ≤ (π/2)|t|/‖u‖`;
* `1 ≤ ‖log u‖ ≤ 3(1 + log|t|)` and `2 log|t| ≤ ‖log u‖` (`norm_logAux_ge_two_log`), so the
  division by `log u` absorbs one logarithm and no more.

The two edges carry the bounds `√(|t|/2π)(6 + log(1+|t|))` at `σ = 0`
(`norm_riemannZeta_mul_I_le`, from the functional equation with the exact modulus of its
`Γ`-factor) and `A |t|^(1/6)(1 + log|t|)` at `σ = 1/2` (item 1), which is exactly the
interpolated exponent `1/2 - 2σ/3` at each edge; at heights `|t| ≤ 3` the edges are compact and
`g` is continuous, so `‖g‖` is bounded there too (`exists_bound_boundary_left`).  Phragmén–
Lindelöf then bounds `‖g‖` on the whole strip, and undoing the two factors gives item 2.

**Removing the logarithm.**  For a fixed `σ` the two subconvex bounds each save a *fixed
positive power* of `|t|` over the convexity exponent `(1-σ)/2`:

* for `1/2 ≤ σ < 1`, `(1-σ)/2 - (1-σ)/3 = (1-σ)/6 > 0`;
* for `0 < σ ≤ 1/2`, `(1-σ)/2 - (1/2 - 2σ/3) = σ/6 > 0`.

Since `1 + log t ≤ (1 + 1/e) t^e` for `t ≥ 1` and `e > 0` (`exists_log_le_rpow`, from
`Real.log_le_rpow_div`), the logarithm is swallowed, giving item 3.  Below the threshold
`10⁹` in the right half the convexity bound is used directly, with `1 + log|t| ≤ 28`.

## No hypothesis

Every theorem of the two files is unconditional; none takes an unproved `Prop` of this
repository as an argument, so `docs/goal/conditional-theorems.txt` is unchanged.

## Adversarial revalidation: M1-SUBCONVEXITY-LEFT

* **Is the statement vacuous?**  No: `0 ≤ σ ≤ 1/2` and `|t| ≥ 3` are satisfiable, the exponent
  is a real power (`Real.rpow`), and the constant is asserted positive.
* **Is it really better than convexity?**  For `σ > 0` the ratio to `|t|^((1-σ)/2)` is
  `|t|^(-σ/6)(1 + log|t|) → 0`; at `σ = 0` the two exponents agree (`1/2`) and the statement is
  the known boundary bound with a different constant.
* **Where does the input come from?**  The left edge is the functional equation
  (`RiemannHypothesis/ImaginaryAxis.lean`, Euler's reflection formula, no Stirling); the
  critical line is `M1-SUBCONVEXITY-UNCONDITIONAL` (van der Corput / Kusmin–Landau), extended
  to all heights here.  Neither is conditional.
* **Does it depend on anything unproved?**
  `#print axioms RiemannHypothesis.norm_riemannZeta_le_subconvexity_left` gives exactly
  `propext, Classical.choice, Quot.sound`; the file has no `sorry`.
* **What is still open?**  Only the pointwise bound is proved, the constant is not explicit
  (it comes from a compactness argument at low height), and the logarithm is not removed at
  fixed `σ = 0`.  Nothing follows for the zeroes.

## Adversarial revalidation: M1-GROWTH

* **Is the claim the one the row asks for?**  The row asks for
  `|ζ(σ + i t)| = O(t^((1-σ)/2))` for `0 < σ < 1` and `t` large.  What is proved is exactly
  that, for each fixed `σ ∈ (0,1)`, in the form `∃ C > 0, ∀ |t| ≥ 3, ‖ζ(σ+it)‖ ≤ C|t|^((1-σ)/2)`.
* **Is the constant uniform in `σ`?**  No, and it cannot be: as `σ → 1` the exponent tends to
  `0` while `ζ(1+it)` is of size `log t`, so no `σ`-uniform constant exists on `(0,1)`.  The
  classical statement is likewise for fixed `σ`.  The row's wording ("for `0 < σ < 1`, `t`
  large") is read that way.
* **Is it vacuous or circular?**  No: it is deduced from two unconditional subconvex bounds,
  neither of which assumes the Riemann hypothesis or any unproved `Prop`.
* **Does it depend on anything unproved?**
  `#print axioms RiemannHypothesis.norm_riemannZeta_le_convexity_logfree` and
  `#print axioms RiemannHypothesis.norm_riemannZeta_le_log_div_of_one_lt_re` give exactly
  `propext, Classical.choice, Quot.sound`.
* **What is still open?**  The Lindelöf exponent `ε` in place of `(1-σ)/2` is not proved and is
  not approached here; the best exponents proved in this repository are `(1-σ)/3` on the right
  half and `1/2 - 2σ/3` on the left half of the strip.  No mean value or zero-density
  consequence is claimed.

## Addendum: one subconvex bound for the whole closed strip

`RiemannHypothesis/SubconvexityClosedStrip.lean` removes the threshold `t ≥ 10⁹` and the sign
restriction from the right-hand bound and merges the two halves:

* `norm_riemannZeta_le_subconvexity_right` : `‖ζ(σ + i t)‖ ≤ C (1 + log|t|) |t|^((1-σ)/3)` for
  `1/2 ≤ σ ≤ 1` and *every* `|t| ≥ 3`.  Below the threshold the convexity bound already gives
  this, because `|t|^((1-σ)/6) ≤ |t|^(1/12) ≤ (10⁹)^(1/12) ≤ 6`
  (`rpow_convexity_le_six_mul_rpow_third`); above it, for `σ < 1`, the conjugation symmetry
  folds `t` to `|t|` and `SubconvexityStrip.norm_riemannZeta_strip_le` applies; on the line
  `σ = 1` the logarithmic bound `‖ζ(1+it)‖ ≤ 6 + log(1+|t|)` covers both signs directly.
* `norm_riemannZeta_le_subconvexity_closed_strip` :
  `‖ζ(s)‖ ≤ C (1 + log|t|) |t|^(max ((1-σ)/3) (1/2 - 2σ/3))` for `0 ≤ σ ≤ 1`, `|t| ≥ 3`.
  The maximum selects `(1-σ)/3` when `σ ≥ 1/2` and `1/2 - 2σ/3` when `σ ≤ 1/2`; the two agree
  at `σ = 1/2`, where the exponent is `1/6`.

## Adversarial revalidation: M1-SUBCONVEXITY-CLOSED-STRIP

* **Is anything new claimed?**  Yes on two counts: the right-hand bound now holds at every
  height `|t| ≥ 3` and for negative `t`, where before it needed `t ≥ 10⁹`; and the two halves
  are merged into one statement covering the closed strip.  The exponents themselves are those
  of `M1-SUBCONVEXITY-STRIP` and `M1-SUBCONVEXITY-LEFT`.
* **Is the merged exponent the right one?**  `max ((1-σ)/3) (1/2 - 2σ/3)` equals `(1-σ)/3`
  exactly when `σ ≥ 1/2`, and `1/2 - 2σ/3` exactly when `σ ≤ 1/2`; it is `1/2` at `σ = 0`
  (no gain over convexity there, as expected), `1/6` at `σ = 1/2` and `0` at `σ = 1`.
* **Does it depend on anything unproved?**
  `#print axioms RiemannHypothesis.norm_riemannZeta_le_subconvexity_closed_strip` gives exactly
  `propext, Classical.choice, Quot.sound`; the file has no `sorry`.
* **What is still open?**  The constant is not explicit, the logarithm stays, the bound is
  pointwise, and no consequence for the zeroes is claimed.

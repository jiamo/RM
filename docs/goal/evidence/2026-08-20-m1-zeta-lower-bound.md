# M1-ZETA-LOWER-BOUND — a quantitative lower bound for ζ to the right of `re s = 1`

Date: 2026-08-20
File: `RiemannHypothesis/ZeroFree.lean`
Gates: `lake build`, `bash scripts/audit.sh`

## What is proved

```lean
theorem norm_riemannZeta_pow_four_ge {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy : 1 ≤ |y|) :
    x ^ 3 / (8 * (6 + Real.log (1 + 2 * |y|))) ≤ ‖riemannZeta (1 + x + I * y)‖ ^ 4

theorem riemannZeta_ne_zero_of_one_lt_re_of_one_le_abs_im
    {x y : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hy : 1 ≤ |y|) :
    riemannZeta (1 + x + I * y) ≠ 0
```

The proof is the classical Mertens argument, made quantitative with the two estimates the
repository already has.  With `A = |ζ(1+x)|`, `B = |ζ(1+x+iy)|`, `C = |ζ(1+x+2iy)|`:

* `A³ B⁴ C ≥ 1` — `RiemannHypothesis.norm_riemannZeta_product_ge_one` (the `3-4-1`
  inequality, specialized from mathlib's Dirichlet-character version at modulus 1);
* `A ≤ 1 + 1/x ≤ 2/x` for `0 < x ≤ 1` — `RiemannHypothesis.norm_riemannZeta_le_of_one_lt_re`;
* `C ≤ 6 + log(1 + 2|y|)` — `RiemannHypothesis.norm_riemannZeta_le_log`, applied at
  `re = 1 + x ∈ (1, 2]` and `im = 2y` with `|2y| ≥ 2`.

Substituting gives `1 ≤ (8/x³) B⁴ L` with `L = 6 + log(1 + 2|y|) > 0`, i.e.
`B⁴ ≥ x³/(8L)`.

## Significance and limits

Mathlib's `riemannZeta_ne_zero_of_one_le_re` already gives nonvanishing on `re s ≥ 1`, but
qualitatively.  The bound above is the quantitative form the de la Vallée Poussin argument
starts from: `|ζ|` on the line `re s = 1 + x` is bounded below by a quantity decaying only
like `x^(3/4) / (log |y|)^(1/4)`.

What is still missing for `M1-ZERO-FREE-REGION` is the transfer *to the left* of the line:
if `β + iy` were a zero with `β` slightly below 1, one compares `ζ(1 + x + iy)` with
`ζ(β + iy) = 0` using a bound for `ζ'` on a disc, i.e. a Borel–Carathéodory/Landau estimate
for `ζ'/ζ`.  Neither that estimate nor the required upper bound for `ζ'` is in mathlib or in
this repository, so the row stays open.

## Verification

* `lake build` succeeds; the file contains no `sorry`.
* `#print axioms` gives exactly `[propext, Classical.choice, Quot.sound]` for both theorems.
* The claims are pinned in `scripts/revalidation.lean` (section `M1-ZETA-LOWER-BOUND`).

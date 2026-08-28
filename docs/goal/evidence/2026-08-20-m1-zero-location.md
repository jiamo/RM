# Evidence: the zeroes of `ζ` above height 4 lie in a strictly narrower strip (2026-08-20)

Row: `M1-ZERO-LOCATION` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/ZeroLocation.lean`, with `c = 2^(-45)` and `L = log|im s|`:

* `zero_re_le_one_sub` : `ζ(s) = 0` and `|im s| ≥ 4` imply `re s ≤ 1 - c/L^9`.
* `zero_le_re` : `ζ(s) = 0` and `|im s| ≥ 4` imply `c/L^9 ≤ re s`.
* `zero_mem_shrinking_strip` : the conjunction of the two.
* `zero_abs_re_sub_half_le` : `|re s - 1/2| ≤ 1/2 - c/L^9`.
* `zero_margin_pos` : the excluded margin `c/L^9` is positive for `|im s| ≥ 4`.

## The argument

The upper bound is the contrapositive of `riemannZeta_ne_zero_of_near_one`
(`M1-ZERO-FREE-REGION-NINTH`).

The lower bound is its reflection. A zero with `|im s| ≥ 4` has `im s ≠ 0`, hence is not one
of the trivial zeroes `-2(n+1)`, hence lies in the open critical strip
(`zero_of_nontrivial_mem_strip`, `M0-TRIVIAL-ZEROS`). The reflection symmetry
`riemannZeta_one_sub_eq_zero_of_mem_strip` (`M0-SYMMETRY`) then gives `ζ(1-s) = 0`, and
`|im (1-s)| = |im s| ≥ 4`, so the upper bound applies to `1-s`:
`1 - re s ≤ 1 - c/L^9`, i.e. `re s ≥ c/L^9`. Note that `log|im (1-s)| = log|im s| = L`, so
the same constant appears on both sides.

## Commands run

```
lake build RiemannHypothesis.ZeroLocation
bash scripts/audit.sh                       # OK
```

`#print axioms` for `zero_mem_shrinking_strip` and `zero_abs_re_sub_half_le` reports exactly
`[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* This is **not** the Riemann hypothesis, nor any approximation to it. The strip proved here
  has width `1 - 2^(-44)/L^9`, which tends to `1` as `|im s| → ∞`; the hypothesis asserts
  width `0`. The excluded margin `2^(-45)/L^9` is minuscule already at moderate heights.
* Nothing at all about zeroes with `|im s| < 4`.
* No counting statement: the number of zeroes in the strip is not bounded here, so
  `M1-ALMOST-ALL-STRIP` is untouched.

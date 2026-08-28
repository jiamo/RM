# M1-ABS-CONV-BOUND evidence

Task: prove an explicit bound for `ζ` on the half-plane of absolute convergence.

Source identity: `RiemannHypothesis/Bounds.lean` (new file, imported by
`RiemannHypothesis.lean`).

What is proved (all without `sorry`):

- `antitoneOn_rpow_neg` : `x ↦ x ^ (-σ)` is antitone on `[1, b]` for `0 < σ`.
- `sum_range_natAddOne_rpow_neg_le` : every partial sum `∑_{n < N} (n+1)^(-σ)` is at
  most `1 + 1/(σ - 1)` for `1 < σ`.  The first term contributes `1` and the rest is
  compared with `∫_1^{1+M} x^(-σ) dx = (1 - (1+M)^(1-σ))/(σ-1) ≤ 1/(σ-1)`
  (`AntitoneOn.sum_le_integral`, `integral_rpow`).
- `tsum_natAddOne_rpow_neg_le` : hence `∑' n, (n+1)^(-σ) ≤ 1 + 1/(σ - 1)`.
- `norm_riemannZeta_le_of_one_lt_re` : `‖ζ(s)‖ ≤ 1 + 1/(re s - 1)` for `1 < re s`,
  from `zeta_eq_tsum_one_div_nat_add_one_cpow` and `‖(n+1)^(-s)‖ = (n+1)^(-re s)`.
- `three_add_four_cos_add_cos_two_nonneg` : `0 ≤ 3 + 4 cos θ + cos 2θ`, the elementary
  Mertens inequality behind the classical zero-free region (the left-hand side equals
  `2 (1 + cos θ)²`).

Commands run:

```bash
lake build
bash scripts/audit.sh
python3 scripts/goal_state.py validate
```

Observed results:

- `lake build`: zero errors; the only `sorry` in the repository is in `Challenge.lean`.
- `audit.sh`: OK; `norm_riemannZeta_le_of_one_lt_re` (now listed in the script)
  depends on exactly `propext, Classical.choice, Quot.sound`.
- `validate`: OK.

Supported claim: `‖ζ(s)‖ ≤ 1 + 1/(re s - 1)` on `re s > 1`.  The bound is finite for
every `s` with `re s > 1` and blows up as `re s → 1⁺`, consistent with the pole.

Not proven: any bound inside the critical strip (`M1-GROWTH` remains open), and
nothing about the growth in `Im s` — the bound above is uniform in `Im s`.

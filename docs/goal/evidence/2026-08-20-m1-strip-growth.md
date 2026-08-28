# M1-STRIP-GROWTH and M1-MERTENS-341 (2026-08-20)

New file: `RiemannHypothesis/Growth.lean`.

## What is proved

| Declaration | Statement |
|---|---|
| `RiemannHypothesis.norm_pairedTerm_le_rpow` | `0 ≤ re s → ‖pairedTerm j s‖ ≤ ‖s‖ (2j+1)^(-(1+re s))` |
| `RiemannHypothesis.tsum_oddAddOne_rpow_neg_le` | `0 < σ → ∑' j, (2j+1)^(-(1+σ)) ≤ 1 + 1/σ` |
| `RiemannHypothesis.norm_dirichletEta_le` | `0 < re s → ‖η(s)‖ ≤ ‖s‖ (1 + 1/re s)` |
| `RiemannHypothesis.norm_one_sub_two_cpow_ge` | `2^(1-re s) - 1 ≤ ‖1 - 2^(1-s)‖` |
| `RiemannHypothesis.norm_riemannZeta_le_of_mem_strip` | `0 < re s < 1 → ‖ζ(s)‖ ≤ ‖s‖ (1 + 1/re s) / (2^(1-re s) - 1)` |
| `RiemannHypothesis.norm_riemannZeta_le_linear_of_mem_strip` | for `0 < σ < 1`, some `C > 0` has `‖ζ(σ+it)‖ ≤ C (1 + \|t\|)` for all real `t` |
| `RiemannHypothesis.norm_riemannZeta_product_ge_one` | `0 < x → 1 ≤ ‖ζ(1+x)³ ζ(1+x+iy)⁴ ζ(1+x+2iy)‖` |

## The argument

The strip bound is elementary and uses only what the repository already had. Each paired
term of the eta series obeys `‖(2j+1)^(-s) - (2j+2)^(-s)‖ ≤ ‖s‖ log((2j+2)/(2j+1)) (2j+1)^(-σ)`
(mean value theorem, `Eta.lean`), and `log((2j+2)/(2j+1)) ≤ 1/(2j+1)`, so the `j`-th term is
at most `‖s‖ (2j+1)^(-(1+σ))`. The odd-index series is dominated term by term, through the
injection `j ↦ 2j`, by the full series `∑ (n+1)^(-(1+σ))`, which `Bounds.lean` bounds by
`1 + 1/σ`. Hence `‖η(s)‖ ≤ ‖s‖ (1 + 1/σ)` on the whole right half-plane.

Inside the strip `‖2^(1-s)‖ = 2^{1-σ} > 1`, so `‖1 - 2^(1-s)‖ ≥ 2^{1-σ} - 1 > 0`, and the
identity `η = (1 - 2^(1-s)) ζ` converts the eta bound into the zeta bound. Explicitly,
`C(σ) = (1 + 1/σ)/(2^{1-σ} - 1)`.

The `3-4-1` bound is obtained from Mathlib's Dirichlet-character product bound
`DirichletCharacter.norm_LFunction_product_ge_one` at modulus `1`, where the L-function is
`ζ` (`DirichletCharacter.LFunction_modOne_eq`). It is *provided by mathlib* in that sense;
what is added here is the zeta-shaped statement that the zero-free-region argument needs.

## Constants, checked by hand

* `σ = 1/2`, `t = 0`: bound `(1/2)(1 + 2)/(√2 - 1) ≈ 3.62`, and `ζ(1/2) ≈ -1.4604`. ✔
* `σ = 1/2`, `t = 14.13` (near the first zero): bound `≈ 14.14 · 3 / 0.414 ≈ 102`, and
  `ζ(1/2 + 14.13i) ≈ 0`. ✔ (The bound is far from sharp; that is expected.)
* `x = 1`, `y = 0`: `ζ(2)^8 ≈ 21.3 ≥ 1`. ✔

## What is *not* proved

The classical convexity bound `|ζ(σ + it)| = O(|t|^((1-σ)/2 + ε))` and the bound
`|ζ(σ + it)| = O(log |t|)` for `1 < σ ≤ 2` are **not** proved: both need the Euler–Maclaurin
approximate functional equation, which the repository does not have. Consequently
`M1-GROWTH` is **not** closed by this work; it is `DONE_WEAK`, and the rows depending on it
(`M1-ZERO-FREE-REGION`, `M1-EXPLICIT`, `M1-HARDY`, `M1-ALMOST-ALL-STRIP`) remain open. The
linear bound proved here does establish that `ζ` is of finite order on every vertical line
strictly inside the strip.

## Commands

```bash
lake build                               # 3190 jobs, success
./scripts/audit.sh                       # OK
lake env lean scripts/revalidation.lean  # no output, exit 0
```

Axioms of the four theorems above: `[propext, Classical.choice, Quot.sound]`.

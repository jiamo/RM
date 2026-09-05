# M1-KUSMIN-LANDAU — the first-derivative test over a *general* range

Date: 2026-09-03
File: `RiemannHypothesis/KusminLandauGeneral.lean` (new)

## What was open

The open boundary of M1-KUSMIN-LANDAU said, in its own words:

> The hypothesis is that `f'` is monotone and trapped between two consecutive integers on the
> whole range; splitting a general range into such subranges is not done here.

`RiemannHypothesis/VanDerCorputSums.lean` does split a range into subranges, but under the
*second-derivative* hypothesis that `f'` grows at speed at least `r > 0`: the blocks where `f'`
is close to an integer are then short, and are counted trivially.  Nothing covered the plain
first-derivative situation — `f'` monotone, at distance at least `λ` from every integer, with no
lower bound on its speed — which is the classical statement of Kusmin and Landau.

## Claim (Lean-checked, no `sorry`)

Write `e(θ) = exp(2πiθ)` (`RiemannHypothesis.KusminLandau.e2pi`).

* `norm_sum_e2pi_le_of_deriv_block` — one block, with the separation hypothesis in place of
  explicit bounds: if `f` has derivative `f'` on `[c, c+K]`, `f'` is monotone there, satisfies
  `λ ≤ |f'(x) − m|` for every integer `m`, and `f'(c+K) < ⌊f'(c)⌋ + 1`, then

      ‖∑_{j ≤ K} e(f(c+j))‖ ≤ 1 + 2/λ .

* `norm_sum_e2pi_le_of_deriv_floor` — the general monotone range, with the number of blocks
  written exactly:

      ‖∑_{j ≤ K} e(f(c+j))‖ ≤ (⌊f'(c+K)⌋ − ⌊f'(c)⌋ + 1) (1 + 2/λ) .

* `norm_sum_e2pi_le_of_deriv_general` — the same for `f'` monotone *or* antitone, in terms of the
  total variation `V = |f'(c+K) − f'(c)|` of the derivative:

      ‖∑_{j ≤ K} e(f(c+j))‖ ≤ (V + 2) (1 + 2/λ) .

This is the classical shape `|∑_{a < n ≤ b} e(f(n))| ≪ (V + 1)/λ` of the first-derivative test for
sums; only the additive constant in the block count differs.

## Proof

Let `k = ⌊f'(c)⌋` and let `m` be the largest index with `f'(c+m) < k + 1` (`Nat.findGreatest`).
On `[c, c+m]` monotonicity gives `f'(c) ≤ f' ≤ f'(c+m) < k + 1`, and the separation hypothesis
upgrades this to `k + λ ≤ f' ≤ k + 1 − λ`: at the left end `f'(c) − k ≥ 0` and its distance to `k`
is at least `λ`, at every point `k + 1 − f'(x) > 0` and its distance to `k+1` is at least `λ`.
So `norm_sum_e2pi_le_of_deriv_sub_int` bounds that block by `1 + 2/λ`, uniformly in its length.
The rest of the range starts at `c + m + 1`, where `f' ≥ k + 1`, so `⌊f'⌋` has grown by at least
one; strong induction on the length of the range therefore gives the block count
`⌊f'(c+K)⌋ − ⌊f'(c)⌋ + 1`.  Finally `⌊b⌋ ≤ b` and `⌊a⌋ > a − 1` turn the count into `V + 2`.

The antitone case is the monotone one applied to `−f`: `e(−θ)` is the complex conjugate of `e(θ)`,
so the two sums have the same norm, and both the separation hypothesis and `V` are unchanged.

## Commands and observed output

```bash
lake build RiemannHypothesis.KusminLandauGeneral   # Build completed successfully
lake build                                          # Build completed successfully (9192 jobs)
./scripts/audit.sh                                  # OK
```

`./scripts/audit.sh` prints, for both new results,

```
'RiemannHypothesis.KusminLandau.norm_sum_e2pi_le_of_deriv_floor' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RiemannHypothesis.KusminLandau.norm_sum_e2pi_le_of_deriv_general' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

and both statements are pinned in `scripts/revalidation.lean`.

## What is *not* proved

* The constant is `(V + 2)(1 + 2/λ)`, not the classical `(V + 1) · 2/λ`; the `+2` comes from the
  two floors and the `1 +` from the boundary term of the summation by parts of the one-block case.
* Nothing here is about `ζ`: no subconvexity bound, no approximate functional equation and no
  density estimate follows, exactly as for the one-block form.  The B process (Poisson summation
  with stationary phase) is still not proved, so the Weyl bound `ζ(1/2 + it) = O(t^(1/6+ε))`
  remains conditional on the approximate functional equation (M1-AFE-SUBCONVEXITY).
* The separation hypothesis is assumed, not derived: for a given phase one still has to show that
  `f'` avoids the integers, which for `f'` sweeping across an integer is false and forces the
  second-derivative test of M1-VDC-SECOND-DERIVATIVE instead.

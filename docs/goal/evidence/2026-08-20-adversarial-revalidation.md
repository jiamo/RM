# Adversarial revalidation of the closed rows (2026-08-20)

Task: `M0-ADVERSARIAL-AUDIT`.

This file is the second, adversarial pass over every row of `docs/goal/task-board.yaml`
that carries the status `DONE_STRONG`. It is referenced from each such row through the
field `revalidation:`, and `python3 scripts/goal_state.py validate` fails if a
`DONE_STRONG` row has no section here.

## Method

The pass is deliberately not a re-reading of status reports. Three mechanical checks and
one human-style check are applied to every closed row.

1. **Statement pinning.** `scripts/revalidation.lean` writes out the full statement of every
   claim of every closed row and supplies the repository's declaration as the proof term
   (`example : <statement written out here> := <declaration>`), and unfolds every definition
   the rows depend on with `rfl`. A renamed, weakened, or extra-hypothesis-carrying
   declaration makes the file stop elaborating. Run by `./scripts/audit.sh`.
2. **Openness.** No proof in the library is left open: `./scripts/audit.sh` greps the whole
   repository, `Challenge.lean` (the statement of record, which the repository's convention
   requires to be unproved there) excepted.
3. **Axioms.** `#print axioms` on every compared theorem; the only admissible output is
   `[propext, Classical.choice, Quot.sound]`.
4. **Constants and hidden assumptions.** Each numerical constant in a closed row is checked
   against a value that can be computed by hand, and the hypotheses of each statement are
   read for vacuity (a hypothesis that cannot be satisfied, or a conclusion that is weaker
   than the row's title claims).

## Commands run

```bash
lake build                               # 3190 jobs, success
./scripts/audit.sh                       # OK
lake env lean scripts/revalidation.lean  # no output, exit 0
python3 scripts/goal_state.py validate   # OK
```

## Global observations

* Exactly three unproved statements exist in the repository, all in `Challenge.lean`, and
  each is proved in `Solution.lean` — as the repository convention requires.
* Every compared theorem depends on exactly `propext`, `Classical.choice`, `Quot.sound`.
* **No row claims the Riemann hypothesis.** No term of type `RiemannHypothesis.ZetaForm`
  exists in the repository. `M4-RH` remains `TODO_NEEDS_DESIGN`.

---

## Adversarial revalidation: M0-GOAL-CONTROL-PLANE

Re-checked: every task carries `milestone`, `depends_on`, `rank`, `exit_criteria`;
`goal_state.py next` returns only dependency-ready rows of the active milestone;
`validate` rejects unknown dependencies, later-milestone dependencies, and cycles. Two new
rules were added to `validate` in this pass (revalidation notes, open-conjecture
reductions) and the board still validates. No hidden assumption: this row is governance
only and claims no mathematics.

## Adversarial revalidation: M0-STATEMENTS

Re-checked by unfolding, not by reading: `revalidation.lean` proves by `rfl` that
`ZetaStripForm`, `EtaForm`, `pairedTerm` and `dirichletEta` are literally the propositions
and series the row claims, and that `ZetaForm` is Mathlib's `RiemannHypothesis`. Vacuity
check: `ZetaStripForm` quantifies over a non-empty region (`ζ` has zeroes in the strip, e.g.
Mathlib's own `riemannZeta` is not identically non-zero there), so the statement is not
vacuous; and none of the three definitions is `True` or defeq to it — each has a
`riemannZeta s = 0` or `dirichletEta s = 0` hypothesis with a non-trivial conclusion
`s.re = 1/2`.

## Adversarial revalidation: M0-CONNECTED

Re-checked: `isPreconnected_punctured_halfPlane : IsPreconnected ({s : ℂ | 0 < s.re} \ {1})`
is pinned with the set written out in full. Hidden-assumption check: the statement has no
hypotheses, so nothing can be smuggled in; the domain really is the punctured half-plane
used by the identity-theorem application in `Eta.lean` (same set expression, checked by
pinning both).

## Adversarial revalidation: M0-ETA

Re-checked: `dirichletEta_eq_mul_riemannZeta` is pinned with both hypotheses
(`0 < re s`, `s ≠ 1`) and the exact right-hand side `(1 - 2^(1-s)) * riemannZeta s`, and
`dirichletEta_eq_tsum_alternating_of_one_lt_re` with the classical alternating series.
Hidden-assumption check: the identity is *not* claimed at `s = 1` (where `ζ` has its pole)
nor for `re s ≤ 0`; the row's title and the docstring agree with the hypotheses.

## Adversarial revalidation: M0-TRIVIAL-ZEROS

Re-checked: `riemannZeta_eq_zero_of_re_nonpos` is pinned with the conclusion
`∃ n : ℕ, s = -2 * (n+1)` — note this excludes `s = 0`, which is correct because
`ζ(0) = -1/2 ≠ 0`, so the statement is not vacuous and not over-strong.
`one_sub_two_cpow_ne_zero` is pinned with hypothesis `re s < 1`; the boundary case
`re s = 1` is genuinely excluded (there `1 - 2^(1-s)` vanishes at `s = 1 + 2πik/log 2`), so
the hypothesis is load-bearing and not decoration.

## Adversarial revalidation: M0-EQUIV

Re-checked: the three equivalences are pinned in `revalidation.lean` through the
`Solution.lean` names (the Challenge namespace), so the audit follows the same path a reader
of `Challenge.lean` would. Claim-mode check: each is an `Iff` between two `Prop`s, neither
side of which is proved; the row does not and cannot claim the conjecture. Axioms of all
three: `[propext, Classical.choice, Quot.sound]`.

## Adversarial revalidation: M0-PARTIAL-STATEMENTS

Re-checked: `ZeroFreeRegion`, `HardyTheorem`, `VerifiedUpToHeight` are unfolded by `rfl`
against the statements written out in `revalidation.lean`. Claim-mode check: every entry of
`RiemannHypothesis/Partial.lean` is a `def ... : Prop`; the repository contains no theorem
whose conclusion is any of them, so nothing here is presented as proved.

## Adversarial revalidation: M0-AUDIT

Re-checked by fault injection reasoning on each of the script's four original checks, and by
extending it: the audit now additionally elaborates `scripts/revalidation.lean` (statement
pinning) and runs the board validator. The unproved-statement grep covers every `.lean` file
outside `.lake`, `Challenge.lean` excepted — including the two scripts added in this pass.

## Adversarial revalidation: M0-SYMMETRY

Re-checked: all eight claims of the row are pinned, with the equivalences stated against the
*written-out* right-hand sides rather than against the abbreviations
(`ZetaUpperStripForm` and friends), so a change in one of those definitions cannot silently
change what the row claims. Hidden-assumption check on
`riemannZeta_ofReal_ne_zero_of_lt_one`: hypotheses `0 < x`, `x < 1`; both are needed
(`ζ(0) ≠ 0` is true but not covered, and `ζ(1)` is the pole), and the conclusion is a
genuine non-vanishing statement, not a vacuous one.

## Adversarial revalidation: M0-ALTERNATING-STRIP

Re-checked: `sum_alternating_eq_pairedSum_add_rem` is pinned including the exact remainder
term `if N % 2 = 0 then 0 else N^(-s)`, and
`tendsto_alternating_partialSum_dirichletEta` is pinned with the hypothesis `0 < re s`
only — that is the point of the row, since inside the strip the series converges
conditionally. Constant check: the remainder bound used in the proof is `N^(-re s)`, which
at `re s > 0` does tend to `0`; at `re s = 0` it does not, and the hypothesis correctly
excludes that.

## Adversarial revalidation: M1-ABS-CONV-BOUND

Re-checked constants by hand: at `σ = 2` the claim gives `‖ζ(2)‖ ≤ 1 + 1/(2-1) = 2`, and
`ζ(2) = π²/6 ≈ 1.645 ≤ 2`; at `σ = 3`, `1 + 1/2 = 1.5` against `ζ(3) ≈ 1.202`. The bound
degenerates as `σ → 1⁺`, as it must because of the pole, so it is not over-strong. The
Mertens inequality `0 ≤ 3 + 4 cos θ + cos 2θ` was re-derived independently:
`3 + 4c + (2c² - 1) = 2(1 + c)² ≥ 0`, with equality at `θ = π`, matching the Lean proof.

## Adversarial revalidation: M1-STRIP-GROWTH

Re-checked constants by hand at `s = 1/2` (real point of the critical line):
the bound reads `‖ζ(1/2)‖ ≤ (1/2)(1 + 2)/(2^{1/2} - 1) ≈ 1.5/0.414 ≈ 3.62`, and
`ζ(1/2) ≈ -1.4604`, so the bound holds and is not vacuous but also not sharp — consistent
with what the row claims. Boundary check: the bound blows up both as `re s → 0⁺`
(the factor `1 + 1/re s`) and as `re s → 1⁻` (the factor `2^{1-re s} - 1 → 0`), which is
honest: the eta representation carries no information at either edge. Claim-mode check: the
row claims a *linear* bound in the height, **not** the classical convexity bound; the row's
`open_boundary` is empty only because the linear bound is the whole of what the row's exit
criteria state, and the sharper estimate stays open on `M1-GROWTH`.

## Adversarial revalidation: M1-MERTENS-341

Provenance check (the important one for this row): the inequality is *derived from Mathlib*
(`DirichletCharacter.norm_LFunction_product_ge_one` at modulus `1`), not proved from scratch
here; the row's evidence and the theorem's docstring both say so, as the claim-hygiene rule
for mathlib-provided results requires. Constant check at `x = 1, y = 0`: the product is
`ζ(2)^8 ≈ 21.3 ≥ 1`. Vacuity check: the hypothesis is `0 < x` only, so the statement covers
the whole half-plane of absolute convergence, and the conclusion is a genuine lower bound.

## Adversarial revalidation: M1-SPECTRAL-INTERPRETATION

Claim-mode check (the decisive one for this row): the row's chain has six steps, of which
three are proved here and three are mathlib results. The evidence file tabulates which is
which, and the docstrings repeat it; in particular the derivation of `Λ(1-s) = Λ(s)` from
the modularity of `θ` happens inside mathlib's abstract functional-equation machinery and is
**not** re-derived here, so the row is closed for *stating the chain with each step checked
or cited*, which is exactly what its exit criteria say. Hypothesis check on the Mellin
representation: `1 < re s` is load-bearing (it is what makes `k = 1/2 < re(s/2)`, hence the
Mellin integral convergent); the statement is false as an identity of convergent integrals
without it. Constant check: at `a = 0` mathlib's kernel is `θ(it)` including the constant
term `1`, which is why the Mellin transform is taken of `(θ(it) - 1)/2` and not of
`θ(it)/2` — the subtraction and the factor `2` were both re-derived by hand against the
classical formula `Λ(s) = π^(-s/2) Γ(s/2) ζ(s)`. Scope check: nothing here mentions the
zeroes, and the file states that Hilbert–Pólya remains conjectural.

## Adversarial revalidation: M0-OPEN-REDUCTION-RULE

Re-checked by fault injection: setting `open_conjecture_reduction: true` on a `DONE_STRONG`
row makes `python3 scripts/goal_state.py validate` fail with an explicit message, and the
board validates again once the flag is removed or the status is lowered. Scope check: the
rule is syntactic, so it is a tripwire, not a proof — the substantive part is the
convention recorded in `docs/goal/goal-prompt.md` §0.4.

## Adversarial revalidation: M0-ADVERSARIAL-AUDIT

Re-checked by fault injection: removing this file, removing a `revalidation:` field, or
deleting one section heading each make `python3 scripts/goal_state.py validate` fail, and
`./scripts/audit.sh` fails with it. Self-reference check: this row's own section is
required by the same rule it introduces, and it is present. Scope check: the gate proves
that a second pass was *recorded*, not that the pass was insightful; the substance is in
the sections above and in the statement pinning of `scripts/revalidation.lean`, which is
machine-checked.

## Adversarial revalidation: M1-EULER-MACLAURIN

Constant check: the three pieces of `norm_riemannZeta_le_log_of_one_lt_re` were re-derived
by hand with `N = ⌈|t|⌉₊`. Truncated sum: `∑_{n<N} (n+1)^(-σ) ≤ H_N ≤ 1 + log N`, and
`N < |t| + 1` gives `log N ≤ log(1 + |t|)` — this needs `N > 0`, which holds because
`|t| ≥ 2`. Pole term: `(N+1)^(1-σ) ≤ 1` uses `σ ≥ 1` and `N + 1 ≥ 1`; `‖s-1‖ ≥ |im(s-1)| =
|t| ≥ 2` gives the factor `1/2`. Tail: `‖s‖ ≤ |σ| + |t| ≤ 2 + |t|` uses `σ ≤ 2`, and
`∑'_n (n+N+1)^(-(1+σ)) ≤ 2/(N+1) ≤ 2/(1+|t|)` uses `1 + σ ≥ 2` and `N ≥ |t|`; the product
is `≤ 2(2+|t|)/(1+|t|) ≤ 4`. Sum `1 + log(1+|t|) + 1/2 + 4 ≤ 6 + log(1+|t|)`. Every
hypothesis of the statement (`1 ≤ re s`, `re s ≤ 2`, `2 ≤ |im s|`) is load-bearing:
dropping `re s ≤ 2` breaks `‖s‖ ≤ 2 + |t|`, dropping `1 ≤ re s` breaks both the harmonic
comparison and `(N+1)^(1-σ) ≤ 1`, and dropping `2 ≤ |im s|` breaks the pole term (the bound
must fail near `s = 1`, where ζ has a pole).

Hidden-assumption check: `riemannZeta_eq_zetaApprox` is proved only for `1 < re s`, where
the Dirichlet series converges absolutely; no analytic continuation is claimed for it, and
none is used. The line `re s = 1` in `norm_riemannZeta_le_log` is obtained by continuity of
`σ ↦ ζ(σ + it)` at `σ = 1` for `t ≠ 0`, which is mathlib's `differentiableAt_riemannZeta`
applied at `1 + it ≠ 1`; the limit is taken along `𝓝[>] 1`, whose `NeBot` instance is what
makes `le_of_tendsto` applicable.

Leakage check: nothing here is conditional on an unproved statement, and nothing about the
zeroes of ζ is claimed — the bound is an unconditional growth estimate. The telescoping
step is the only place where a limit is used, and it is justified by `g n → 0`, which needs
`re s > 1`; it is not silently reused on the line `re s = 1`.

## Adversarial revalidation: M1-ZETA-LOWER-BOUND

Constant check: with `A = |ζ(1+x)|`, `B = |ζ(1+x+iy)|`, `C = |ζ(1+x+2iy)|` and
`L = 6 + log(1+2|y|)`, the chain is `1 ≤ A³B⁴C ≤ (2/x)³B⁴L = 8B⁴L/x³`, hence
`B⁴ ≥ x³/(8L)`. The step `A ≤ 1 + 1/x ≤ 2/x` needs `x ≤ 1`, which is a hypothesis; the step
`C ≤ L` needs `1 < 1+x ≤ 2` (so `x ≤ 1` again) and `|2y| ≥ 2` (so `|y| ≥ 1`, a hypothesis).
`L > 0` because `log(1+2|y|) ≥ 0`. Every hypothesis is therefore load-bearing.

Direction check: the conclusion is a *lower* bound, so the two cited estimates must be used
as *upper* bounds on the other two factors — the inequality is reversed by dividing, and the
positivity of `A`, `B`, `C` and `L` is what makes the reversal valid; each of those four
positivity facts appears explicitly in the proof.

Leakage check: this is a statement about `re s > 1` only. It is *not* a zero-free region:
nothing is claimed at or to the left of `re s = 1`, and the evidence file names the missing
ingredient (a bound for `ζ'`, equivalently a Borel–Carathéodory/Landau estimate for `ζ'/ζ`).
The corollary `riemannZeta_ne_zero_of_one_lt_re_of_one_le_abs_im` is derived from the bound
rather than cited from mathlib's `riemannZeta_ne_zero_of_one_le_re`, so it carries no hidden
dependency on the qualitative result.

## Adversarial revalidation: M1-ZETA-CONTINUATION

Claim-mode check: `riemannZeta_eq_zetaApprox_of_pos_re` is a *proof*, not a statement, and
it is proved here rather than cited: mathlib has no Euler–Maclaurin representation of `ζ`.
Domain check: the identity is claimed on `{s | 0 < re s} \ {1}` and no further; `s = 1` is
excluded because `zetaApprox N` has the factor `1/(s-1)` and `ζ` has its pole there, and
`re s ≤ 0` is excluded because the tail `∑' n, eulerTerm (n+N) s` diverges there (the term
bound is `‖s‖ (n+1)^(-(1+re s))`, summable exactly for `re s > 0`).

Hypothesis check: both hypotheses are load-bearing. Dropping `s ≠ 1` makes the right-hand
side undefined in the intended sense (division by zero in Lean, so the identity would be a
false statement about `ζ(1)`, which mathlib sets to a finite value); dropping `0 < re s`
breaks the summability that `differentiableOn_tsum_eulerTerm` needs.

Mechanism check: the identity theorem is applied exactly as in `M0-ETA` — the two sides are
`AnalyticOnNhd` on the punctured half-plane, the domain is preconnected
(`isPreconnected_punctured_halfPlane`), and they agree on a neighbourhood of `s = 2`, since
`riemannZeta_eq_zetaApprox` holds on the open set `{1 < re s}`. No circularity: that input
identity is proved only for `1 < re s`, and the continuation is not used to prove it.

## Adversarial revalidation: M1-NEARLINE-LOG-BOUND

Constant check, re-derived by hand with `σ = re s`, `t = |im s|`, `L = log t ≥ 1`,
`N = ⌈t⌉₊` (so `t ≤ N < t+1`): the region hypothesis `σ ≥ 1 - 1/(2L)` gives
`N^(1-σ) = exp((1-σ) log N) ≤ exp(log(t+1)/(2L)) ≤ exp(1) ≤ 3`, using `log(t+1) ≤ 2L`,
which is `t + 1 ≤ t²` for `t ≥ 3`. Then the Dirichlet sum is
`∑_{n<N}(n+1)^(-σ) ≤ N^(1-σ) ∑_{n<N}(n+1)^(-1) ≤ 3(1 + log N) ≤ 3 + 6L`; the pole term is
`(N+1)^(1-σ)/‖s-1‖ ≤ 3/t ≤ 1` (using `‖s-1‖ ≥ |t| ≥ 3`); the tail is
`‖s‖ ∑'_n (n+N+1)^(-(1+σ)) ≤ (1+t) · N^(-σ)/σ ≤ (1+t)(3/t)/(1/2) ≤ 8` (using `σ ≥ 1/2`,
which follows from `σ ≥ 1 - 1/(2L)` and `L ≥ 1`). Total `12 + 6L ≤ 18L`. Every one of the
three hypotheses is load-bearing: without `re s ≥ 1 - 1/(2 log|t|)` the factor `N^(1-σ)`
is unbounded (the true size is `≍ |t|^(1-σ)`), without `re s ≤ 2` the appeal to the earlier
`norm_riemannZeta_le_log` on `1 ≤ re s ≤ 2` fails, and without `3 ≤ |im s|` both `L ≥ 1`
and the pole estimate fail.

Non-vacuity check: the region is non-empty — for instance `s = 1 + 3i` satisfies all three
hypotheses — and the bound is not trivially true, since `18 log|t| → ∞` only logarithmically
while the strip bound available before this row was linear in `|t|`.

Tail-lemma check: `tsum_shift_rpow_neg_le_rpow` is proved by comparison with the integral
and re-derived by hand: `∑_{i<M} (N+i+1)^(-p) ≤ ∫_N^{N+M} x^(-p) dx = (N^(1-p) -
(N+M)^(1-p))/(p-1) ≤ N^(1-p)/(p-1)`, valid for `p > 1` and `N ≥ 1`; the earlier
`tsum_shift_rpow_neg_le` needed `p ≥ 2` and is not used here.

## Adversarial revalidation: M1-ZERO-FREE-REGION-NINTH

Constant check: `576⁴ = 110075314176`, `64 · 576⁴ = 7044820107264` and
`2⁴⁵ = 35184372088832`, so `64 · 576⁴ · 2^(-45) ≈ 0.2003 < 1`, which is exactly the
inequality that closes the proof; the margin is a factor of about `5`, so the constant
`2^(-45)` is not on a knife edge. The chain of constants: `‖ζ‖ ≤ 18 log|t|` on the region,
`36 log|t|` on the Cauchy circle of radius `r = 1/(8 log|t|)` (because `log|im w| ≤ 2 log|t|`
there), hence `‖ζ'‖ ≤ 36 log|t| / r = 288 (log|t|)²`; the mean value inequality over a
segment of length `1 + x - re s ≤ 2x` gives `576 (log|t|)² x`; the Mertens lower bound gives
`x³/(8(6 + log(1+2|t|))) ≥ x³/(64 log|t|)`.

Radius check: the Cauchy disc must stay inside the region where the logarithmic bound holds.
With `r = 1/(8 log|t|)` and centre `re s ≥ 1 - 1/(8 log|t|)`, every point `w` of the closed
disc has `re w ≥ 1 - 1/(4 log|t|) ≥ 1 - 1/(2 log|im w|)` — the last step uses
`log|im w| ≤ 2 log|t|`, which needs `|im w| ≤ 2|t|` and hence `|t| ≥ 4`, one of the
hypotheses — and `re w ≤ 5/4 + 1/8 ≤ 2`, and `|im w| ≥ |t| - 1/8 ≥ 3`. So the disc is inside
the region, and it avoids the pole `s = 1`.

Hypothesis and claim-mode check: `4 ≤ |im s|` is load-bearing (it gives `log|t| ≥ 1` and the
radius control); the region hypothesis is the conclusion's own content. The case `re s ≥ 1`
is *cited* from mathlib (`riemannZeta_ne_zero_of_one_le_re`) and is labelled as such in the
source; everything to the left of the line is proved here. The result is strictly weaker
than the row `M1-ZERO-FREE-REGION` (exponent `9`, not `1`), and that row is *not* closed by
it: it remains `DONE_WEAK` with its `open_boundary` naming the missing Landau /
Borel–Carathéodory estimate.

Leakage check: nothing here is conditional on an unproved statement, and nothing implies the
Riemann hypothesis — the region has width `→ 0` as `|t| → ∞`, so it is compatible with
zeroes arbitrarily close to the line.

## Adversarial revalidation: M1-STRIP-TRIVIAL-BOUND

Claim pinned in `scripts/revalidation.lean`:
`0 < re s → re s ≤ 1 → 3 ≤ |im s| → ‖ζ(s)‖ ≤ 8 / re s * |im s|^(1 - re s) * (1 + log|im s|)`.

Non-vacuity check: the hypotheses are satisfiable — `s = 1/2 + 3i` has `re s = 1/2 ∈ (0,1]`
and `|im s| = 3` — so the statement is not vacuous. It is also not trivially true: the
right-hand side is `o(|t|)` for every fixed `σ > 0`, so it is strictly stronger than the
linear bound `C(σ)(1 + |t|)` of `M1-STRIP-GROWTH` that this row supersedes, and at `σ = 1`
it reads `8(1 + log|t|)`, of the same logarithmic quality as `M1-EULER-MACLAURIN`.

Hypothesis check: all three hypotheses are load-bearing. `0 < re s` is needed for the
Euler–Maclaurin representation of `M1-ZETA-CONTINUATION` to hold at all and for the tail
`∑' (n+N+1)^(-(1+σ))` to converge; it also appears as the `8/σ` blow-up on the right, which
is genuine: the Euler–Maclaurin tail is only summable because `σ > 0`, and its bound carries
the factor `1/σ`, so the estimate necessarily degenerates as `σ → 0`.
`re s ≤ 1` is used only through `strip_bound_arith` (via `6/σ ≥ 6` and `8/σ ≥ 2`), and
`3 ≤ |im s|` gives both `log|im s| ≥ 1` and `‖s - 1‖ ≥ |im s| ≥ 3`, without which the pole
term is unbounded. The case `s = 1` is excluded automatically: `3 ≤ |im s|` forces `s ≠ 1`,
and the proof derives `hs1 : s ≠ 1` from it rather than assuming it.

Constant check, recomputed independently. With `T = t^(1-σ)`, `L = log t`, the three pieces
are `2T(2+L)`, `T`, `(2/σ)T`; their sum is `(2(2+L) + 1 + 2/σ)T = (5 + 2L + 2/σ)T`. The
claimed bound is `(8/σ)(1+L)T = (8/σ + (8/σ)L)T`. Since `σ ≤ 1`, `8/σ = 2/σ + 6/σ ≥ 2/σ + 6`,
which already exceeds `5 + 2/σ`, and `(8/σ)L ≥ 8L ≥ 2L`. So the inequality holds with slack
at least `(1 + 6L)T`. No knife edge.

Truncation check: `N = ⌈t⌉₊` satisfies `t ≤ N < t + 1 ≤ 2t` (the last step uses `t ≥ 1`),
which is the only property of `N` used; the identity `ζ(s) = zetaApprox N s` holds for
*every* `N`, so no circularity or hidden optimality is involved. The two rescalings
`N^(1-σ) ≤ (2t)^(1-σ) = 2^(1-σ) t^(1-σ) ≤ 2 t^(1-σ)` and
`log N ≤ log(2t) = log 2 + log t ≤ 1 + log t` are both valid for `0 ≤ 1 - σ ≤ 1`.

Claim-mode check: the statement is proved outright, with no cited-but-unproved input beyond
mathlib and the earlier rows of this repository (`M1-ZETA-CONTINUATION` for the
representation, `M1-NEARLINE-LOG-BOUND` for `tsum_shift_rpow_neg_le_rpow` and
`one_le_log_of_three_le`, `M1-EULER-MACLAURIN` for `norm_eulerTerm_le` and
`sum_range_natAddOne_rpow_neg_le_one_add_log`), all of which are themselves closed rows.

Leakage check: `M1-GROWTH` is *not* closed by this row. Its first exit criterion asks for
exponent `(1-σ)/2`; what is proved is exponent `1 - σ`. `M1-GROWTH` stays `DONE_WEAK` with
its `open_boundary` rewritten to name exactly that factor-of-two gap. Nothing here implies
the Riemann hypothesis, or even the Lindelöf hypothesis, which would require the exponent
to be `ε` at `σ = 1/2`.

## Adversarial revalidation: M1-ZERO-LOCATION

Claims pinned in `scripts/revalidation.lean`:
`ζ(s) = 0 → 4 ≤ |im s| → 2^(-45)/L^9 ≤ re s ≤ 1 - 2^(-45)/L^9` and the equivalent
`|re s - 1/2| ≤ 1/2 - 2^(-45)/L^9`, where `L = log|im s|`.

Non-vacuity check: the hypotheses are satisfiable in principle — `ζ` has zeroes with
`|im s| ≥ 4` (the first has `im ≈ 14.13`), and that fact is classical, not needed for the
proof. The statement is a conditional about zeroes, so it would be vacuous only if `ζ` had
no zeroes above height 4; the proof does not depend on which of the two is the case, and no
existence claim is made or used here.

Strength check: is the conclusion stronger than what was already available? Yes, but only
just. `zero_of_nontrivial_mem_strip` already gives `0 < re s < 1` (strict, but with no
quantitative margin). What is added is the explicit margin `2^(-45)/L^9` on each side, which
is what makes the containment a *closed* strip strictly inside the open critical strip.
The margin is tiny: at `|im s| = 10^6`, `L ≈ 13.8`, `L^9 ≈ 1.3 · 10^10`, so the margin is
about `2 · 10^(-24)`. The statement is therefore honest but weak, and is labelled as such.

Reflection check: the reflection step needs `ζ(s) = 0 → ζ(1-s) = 0`, which
`riemannZeta_one_sub_eq_zero_of_mem_strip` supplies only for `0 < re s < 1`. That hypothesis
is discharged, not assumed: `|im s| ≥ 4` gives `im s ≠ 0`, which rules out the trivial
zeroes `-2(n+1)` (all real), and `zero_of_nontrivial_mem_strip` then puts `s` in the strip.
No circularity: the reflection lemma is proved in `RiemannHypothesis/Symmetry.lean` from the
completed zeta functional equation, independently of the zero-free region.

Constant check: `L` is unchanged under reflection because `im(1-s) = -im s`, so
`|im(1-s)| = |im s|`; the constant on the left is therefore exactly the constant on the
right, with no loss. The conversion to `|re s - 1/2| ≤ 1/2 - 2^(-45)/L^9` is the pair of
inequalities rewritten, nothing more.

Claim-mode check: everything is proved outright from closed rows of this repository
(`M1-ZERO-FREE-REGION-NINTH`, `M0-SYMMETRY`, `M0-TRIVIAL-ZEROS`) plus mathlib.

Leakage check: nothing here implies the Riemann hypothesis. The strip has width
`1 - 2^(-44)/L^9 → 1`, so it is compatible with zeroes arbitrarily close to `re s = 0` and
`re s = 1`. `M1-ALMOST-ALL-STRIP` remains open — no zero *counting* is proved.

## Adversarial revalidation: M1-PNT-REDUCTION

Claims pinned in `scripts/revalidation.lean`: three implications, ending with
`ψ(x)/x → 1 → π⌊x⌋/(x/log x) → 1`.

Claim-mode check — the most important one here. These are **implications**, not theorems
about primes. The hypothesis `ψ(x) ~ x` is logically equivalent to the prime number theorem,
so nothing about the distribution of primes is established. The row is closed as
`DONE_STRONG` because what it claims — the reduction — is fully proved; `M1-PNT` itself
stays `TODO_READY`, and its `open_boundary` now names `ψ(x) ~ x` as the single remaining
input. No status anywhere asserts the prime number theorem.

Non-vacuity check: the hypothesis is *not* known-false, and in fact is true, so the
implications are not vacuous; but neither is it available in this repository or in mathlib,
so the conclusion cannot be detached. An implication with an unprovable-here hypothesis is
exactly what this row claims, and the pinning makes that visible: each pinned `example` has
an arrow in it.

Content check: is the reduction non-trivial, or does it hide the difficulty? It is genuinely
elementary and complete. Step one uses `|ψ - θ| ≤ 2√x log x`, an explicit Chebyshev estimate
proved in mathlib by counting prime powers, and `log =o[atTop] x^(1/2)`. Step two uses
mathlib's Abel-summation identity `π⌊x⌋ = θ(x)/log x + ∫₂ˣ θ(t)/(t log²t) dt` in its `IsBigO`
form. No circular appeal to any zeta-function input is made; in particular this row does not
depend on the zero-free region rows, and its `depends_on` reflects that.

Statement-shape check: the conclusion is stated with `Nat.primeCounting ⌊x⌋₊` for real `x`,
matching mathlib's `π ⌊x⌋₊` and the exit criterion of `M1-PNT`; it is *not* weakened to a
statement along the natural numbers only, and the normalization `x / log x` is the standard
one.

Leakage check: nothing here bears on the Riemann hypothesis. Even the full prime number
theorem is far weaker than RH, which is equivalent to the error term `ψ(x) - x = O(x^(1/2+ε))`.

# Evidence: the de Bruijn–Newman family and the constant Λ (2026-08-20)

Row: `M2-DE-BRUIJN-NEWMAN` (`DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/DeBruijnNewman.lean`:

* `dbnTerm n u = (2 π² n⁴ e^{9u} − 3 π n² e^{5u}) e^{−π n² e^{4u}}` and
  `dbnPhi u = ∑_{n ≥ 1} dbnTerm n u` — the de Bruijn–Newman weight `Φ` (definitions).
* `dbnKernel t z u = e^{t u²} Φ(u) cos(u z)` and
  `dbnH t z = ∫_0^∞ e^{t u²} Φ(u) cos(u z) du` — the family `H_t` (definitions).
* `dbnLambda = sInf {t | every zero of H_t is real}` — the de Bruijn–Newman constant `Λ`
  (definition).
* `summable_dbnBound`, `abs_dbnTerm_le_of_mem_Icc`, `abs_dbnTerm_le_of_nonneg` : a summable
  majorant for the terms of `Φ`, uniform on `[0, A]` and with the decay factor made
  explicit on `[0, ∞)`.
* `abs_dbnPhi_le` : `|Φ(u)| ≤ C e^{9u} e^{−π e^{4u}}` for `u ≥ 0`, with the explicit
  constant `C = dbnConst = e^π ∑_n dbnBound n`.
* `continuousOn_dbnPhi_Icc`, `continuousOn_dbnPhi_Ioi` : `Φ` is continuous on `(0, ∞)`.
* `exp_neg_pi_exp_le` : `e^{−π e^{4u}} ≤ e^{−2u³}` for `u ≥ 0`.
* `norm_ccos_le`, `norm_csin_le` : `‖cos w‖, ‖sin w‖ ≤ e^{‖w‖}`.
* `norm_dbnKernel_le`, `norm_dbnKernelDeriv_le` : pointwise bounds
  `‖e^{tu²} Φ(u) cos(uz)‖ ≤ C e^{t u² + (9 + ‖z‖) u − 2u³}` and the same with `10` in place
  of `9` for the `z`-derivative of the integrand.
* `integrableOn_dbnKernel` : the integral defining `H_t(z)` converges absolutely, for every
  real `t` and every complex `z`.
* `differentiable_dbnH` : **for every real `t`, `z ↦ H_t(z)` is entire.**
* `dbnH_neg` : `H_t(−z) = H_t(z)`, since the cosine is even.
* `dbnH_conj`, `dbnH_conj_eq_zero` : `H_t(conj z) = conj H_t(z)` (the weight and the Gaussian
  factor are real), so the zero set of `H_t` is symmetric about the real axis.

## Statements recorded, not proved

* `DeBruijnNewmanEquivRH : Prop` — `ZetaForm ↔ Λ ≤ 0` (de Bruijn 1950, Newman 1976).
* `DeBruijnNewmanNonnegative : Prop` — `0 ≤ Λ` (Rodgers–Tao 2018).

These are `def ... : Prop`, in the same spirit as `RiemannHypothesis/Partial.lean`: the
repository writes down what the literature proves without claiming it here. No term of
either type is constructed anywhere in the repository.

## The argument

The whole analytic content is the decay of `Φ`. For `u ≥ 0` and `m = n + 1 ≥ 1`,

```
|(2π²m⁴e^{9u} − 3πm²e^{5u}) e^{−πm²e^{4u}}| ≤ (2π²m⁴ + 3πm²) e^{9u} e^{−πm²e^{4u}},
```

and `πm²e^{4u} ≥ πm² + πe^{4u} − π` because `(m² − 1)(e^{4u} − 1) ≥ 0`, so each term is at
most `e^π · dbnBound n · e^{9u} e^{−πe^{4u}}` with
`dbnBound n = (2π²m⁴ + 3πm²) e^{−πm²}` summable (comparison with
`∑ n^k e^{−πn}`). Summing gives `abs_dbnPhi_le`.

Since `e^{4u} ≥ (4u/3)³ · (1/…)`, one gets `π e^{4u} ≥ 2u³` for `u ≥ 0` (using `π > 3` and
`e^x ≥ 1 + x`), i.e. `e^{−πe^{4u}} ≤ e^{−2u³}`; combined with `‖cos(uz)‖ ≤ e^{u‖z‖}` this
majorizes the integrand by `C e^{t u² + (9 + ‖z‖)u − 2u³}`, which is integrable on
`(0, ∞)` because the cubic beats the quadratic. The same estimate for the `z`-derivative,
uniform for `w` in the unit ball around `z`, lets
`hasDerivAt_integral_of_dominated_loc_of_deriv_le` differentiate under the integral sign,
which gives `differentiable_dbnH`.

## Commands run

```
lake build RiemannHypothesis.DeBruijnNewman
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for `abs_dbnPhi_le`, `integrableOn_dbnKernel` and `differentiable_dbnH`
reports exactly `[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* The identification `H_0 = Ξ` (up to normalisation) is **not** proved; it requires the
  Fourier-integral representation of the completed zeta function.
* `DeBruijnNewmanEquivRH` and `DeBruijnNewmanNonnegative` are **not** proved; both are
  recorded as `Prop`s. In particular nothing here says that the set
  `{t | all zeroes of H_t are real}` is nonempty, so `dbnLambda`, being an `sInf` of a set
  that is not proved nonempty, carries no proved lower bound — this is exactly why the two
  statements above are the open content of the row.

## Adversarial revalidation: M2-DE-BRUIJN-NEWMAN

Second, independent pass.

* **Claim mode.** `dbnTerm`, `dbnPhi`, `dbnKernel`, `dbnH`, `dbnLambda`, `dbnConst`,
  `dbnBound`, `dbnKernelDeriv` are `def`s; `DeBruijnNewmanEquivRH` and
  `DeBruijnNewmanNonnegative` are `def ... : Prop`, i.e. *statements*. Everything else in
  the file is a `theorem`/`lemma` proved here. `scripts/revalidation.lean` pins each
  definition by `rfl` and supplies the repository's declarations as the proof terms of the
  proved statements, so a weakening cannot go unnoticed.
* **Non-vacuity.** `differentiable_dbnH` quantifies over *all* real `t` and all `z ∈ ℂ`
  with no side condition, and it is not vacuous: `integrableOn_dbnKernel` shows the
  integral that defines `H_t` is an honest absolutely convergent integral rather than the
  junk value of a divergent one. The hypothesis `0 ≤ u` in the pointwise estimates is
  harmless because the domain of integration is `(0, ∞)`.
* **Where the sign matters.** `Φ` is not of one sign — the term `−3πn²e^{5u}` dominates for
  small `u` — so only `|Φ|` is estimated; no positivity of `Φ` is claimed or used.
* **Numerical sanity.** At `u = 0` the first term is `2π² − 3π ≈ 10.31` times `e^{−π}`,
  about `0.446`; the second is `(2π²·16 − 3π·4)e^{−4π} ≈ 278 · 3.5·10^{−6} ≈ 0.001`, so the
  series converges extremely fast, consistent with `dbnBound`. The decay claim
  `e^{−πe^{4u}} ≤ e^{−2u³}` at `u = 1` reads `e^{−171.5} ≤ e^{−2}`, and at `u = 0` it reads
  `e^{−π} ≤ 1`. Both hold with enormous room, as they must: the true decay is
  doubly exponential.
* **The `sInf` caveat is recorded, not hidden.** `dbnLambda` is defined as an infimum over
  a set whose nonemptiness (de Bruijn's `t ≥ 1/2` result) is not proved here; consequently
  the row proves nothing about the *value* of `Λ`, and the evidence above says so
  explicitly. The two literature statements remain `Prop`s, so no reduction to an open
  conjecture is being used to close anything.

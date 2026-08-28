# Evidence: the ordinates of the zeroes on the critical line are unbounded (2026-08-21)

Row: `M1-CRITICAL-LINE-ORDINATES` (new, `DONE_STRONG`).

## What is proved (without `sorry`)

`RiemannHypothesis/CriticalLineOrdinates.lean`, writing
`criticalLineZeroSet = {ρ | ζ ρ = 0, re ρ = 1/2}` and
`simpleCriticalLineZeroSet` for its simple members:

* `finite_windowZeros` : the zeroes with ordinate in a window `(T₁, T₂]` form a finite set;
* `exists_mem_criticalLineZeroSet_lt_im` : **above every height `T` there is a zero of `ζ` on the
  critical line** — `∃ s ∈ criticalLineZeroSet, T < im s`;
* `exists_mem_simpleCriticalLineZeroSet_lt_im` : the same with the zero *simple*;
* `conj_mem_criticalLineZeroSet`, `exists_mem_criticalLineZeroSet_im_lt` : the line's zero set is
  stable under conjugation, hence below every height there is a zero on the line too;
* `riemannXi_ofReal_eq_zero_iff` : a real `t` is a zero of `Ξ` exactly when `1/2 + i t` is a zero
  of `ζ` on the line;
* `infinite_setOf_riemannXi_ofReal_eq_zero` : **`Ξ` has infinitely many real zeroes**;
* `exists_riemannXi_ofReal_eq_zero_lt`, `exists_riemannXi_ofReal_eq_zero_gt` : above every height
  there is a real zero of `Ξ`, and below every height there is one too;
* `not_bddAbove_setOf_riemannXi_ofReal_eq_zero`, `not_bddBelow_setOf_riemannXi_ofReal_eq_zero` :
  equivalently, the set of real zeroes of `Ξ` is bounded neither above nor below.

## The argument

Hardy's theorem (`M1-HARDY`) says the zero set on the line is infinite, which by itself does not
locate the zeroes. The location comes from the *window* counts.

* *Unboundedness above.* Suppose every zero on the line had ordinate at most `T`, and put
  `T₀ = max T 0`. Then for every `T'` the set counted by `windowCountOnLine 0 T'` is contained in
  the one counted by `windowCountOnLine 0 T₀` (an element has `0 < im ≤ T ≤ T₀`), and the latter is
  finite by `finite_windowZeros`, so `T' ↦ windowCountOnLine 0 T'` would be bounded — contradicting
  `tendsto_windowCountOnLine_atTop`. The simple-zero statement is the same argument with
  `tendsto_windowCountSimpleOnLine_atTop`.
* *Unboundedness below.* Conjugation maps the line's zero set to itself
  (`conj_mem_nontrivialZeroSet` from `M0-SYMMETRY`, plus `(conj s).re = s.re`) and negates the
  ordinate, so the statement above `-T` gives one below `T`.
* *The `Ξ` form.* For real `t`, `xiPoint t = 1/2 + i t` has real part `1/2`, so
  `riemannXi_eq_zero_iff` (`M0-XI`) collapses to "`ζ` vanishes at `1/2 + i t`". Every zero `s` on
  the line is `xiPoint (im s)`, so `criticalLineZeroSet` is contained in the image of the real
  zero set of `Ξ` under `t ↦ xiPoint t`, and an infinite image forces an infinite source.

## Commands run

```
lake build RiemannHypothesis.CriticalLineOrdinates
lake build
bash scripts/audit.sh                       # OK
```

`#print axioms` for each result above reports exactly `[propext, Classical.choice, Quot.sound]`.

## What is *not* proved

* **No height is exhibited.** The statements are pure existence: they inherit the
  non-effectivity of the divergence of the counting functions, and no numerical ordinate (such as
  the classical `14.13…`) is produced.
* **No density or spacing.** Nothing is said about how many zeroes lie above a given height beyond
  "at least one", nor about gaps between consecutive ordinates.
* **Nothing about the remaining zeroes.** The results concern only zeroes already known to be on
  the line; they bear on the Riemann hypothesis not at all.

## Adversarial revalidation: M1-CRITICAL-LINE-ORDINATES

Second, independent pass.

* **Claim mode.** All results are `theorem`s of this repository, pinned in full in
  `scripts/revalidation.lean` with the repository declarations as proof terms; `scripts/audit.sh`
  prints their axioms.
* **Vacuity check.** Each conclusion is an existence statement about a *nonempty* object, so it
  cannot hold vacuously; in particular `exists_mem_criticalLineZeroSet_lt_im T` produces a zero for
  arbitrary real `T`, including large positive `T`, where the finite-set argument would otherwise
  fail.
* **Is the contradiction genuine?** The two unboundedness proofs are by contradiction, and the
  contradiction is between a *bounded* count and a divergent one — not between the hypothesis and
  itself. Removing the divergence input leaves the goals unprovable, so it is load-bearing.
* **Could the `Ξ` statement be about the wrong function?** `riemannXi_ofReal_eq_zero_iff` is proved
  from `M0-XI`'s `riemannXi_eq_zero_iff`, whose right-hand side names `riemannZeta` explicitly, and
  the pinned statement mentions `riemannXi` and the coercion `(t : ℂ)` in full; a mismatch of
  normalisation would be visible there.
* **Is the conjugation step needed?** Yes for the "below every height" statement; the "above"
  statement never uses it, so the two are independent and a failure of one would not silently
  carry the other.
* **Sanity check against the literature.** Classically the ordinates of the zeroes on the line are
  unbounded (indeed `N₀(T) ≫ T log T`), and infinitely many of them are simple; the statements
  here are the qualitative shadow of that, and nothing stronger is claimed.

# Review of the parts that were already counted as done

This note answers, in the order they were asked, four questions about the *finished* part of the
repository — the part no task-board row was watching — and records what was changed.  Everything
below was re-run on these sources; `bash scripts/audit.sh` prints `OK`.

## 4. Does it compile?  (done first, because nothing else means anything otherwise)

**It did not, as delivered.**  `lake build` refused to start: `lake-manifest.json` disagreed with
the project's own pins.  It recorded Mathlib at a different revision (and under a different URL)
than `lakefile.toml` asks for, and it did not mention the vendored `Zeta23` path dependency at all,
so Lake reported `dependency 'Zeta23' not in manifest`.

Fixed by re-resolving the dependencies against the project's own pins — `lean-toolchain`
(`leanprover/lean4:v4.33.0`) and `lakefile.toml` (Mathlib `db584cd…`, the `v4.33.0` tag) are
unchanged; only `lake-manifest.json` differs.  With that:

* `lake build` — **completed successfully, 9200 jobs**, no errors;
* the eleven modules merged in the last three rounds all compile; there is **no API drift**.  The
  only diagnostics are deprecation notices from Mathlib (`Set.mem_setOf_eq → Set.mem_ofPred_eq`,
  `Set.Finite.diff → Set.Finite.sdiff`, `push_neg → push Not`, …), which are warnings, not errors,
  and are fixed in the files touched here;
* the only `declaration uses 'sorry'` warnings are the three deliberate ones in `Challenge.lean`.

The worry about the source repository pinning Mathlib `v4.28.0` did not materialise: the vendored
`Zeta23` pins the same `v4.33.0` Mathlib as this repository, and its `AUDIT.md` records
`v4.33.0-rc2`, one release candidate earlier; everything elaborates against `v4.33.0`.

## 2. Axiom-audit coverage: 719 of 2030, hand-maintained

Confirmed, and now closed as a *class* of risk rather than patched.

* Measured: the hand-written list in `scripts/audit.sh` carried 719 `#print axioms` lines against
  2030 exported theorems — 35 %.
* **New: `scripts/axiom_audit.lean`.**  It walks the environment, and for every theorem declared in
  a module of this repository (`RiemannHypothesis*`, `Solution`) it collects the axioms the proof
  actually uses, exactly as `#print axioms` does, and reports anything outside `propext`,
  `Classical.choice`, `Quot.sound`.  Current result: **2255 theorems checked, 0 outside the
  standard three.**  A new theorem is covered the moment it is written; no list to update.
  It is step 3b of `scripts/audit.sh`.
* **Positive control** (the check that the check can fail): a `theorem … := by sorry` was added to a
  leaf module and the library rebuilt; the audit reported
  `NONSTANDARD RiemannHypothesis.audit_positive_control_tmp : [sorryAx]` and exited the `OK` branch.
  The control was then removed.
* The old pinned list is kept — it names the results the repository is compared on — and its
  coverage is now reported (step 3c, `scripts/list_theorems.lean` + `scripts/audit_coverage.py`).
  That step also **fails** the audit if a pinned name is no longer exported, since `#print axioms`
  of an unknown name checks nothing: four such stale names were found and fixed while writing it.
* The 28 lines added by the six subconvexity files were among the names checked; all of them
  resolve, and all print the standard three.

## 1. The vendored `Zeta23`: is the two-thirds theorem real, or a definitional artefact?

Three separate checks, all recorded in
`docs/goal/evidence/2026-09-06-m1-two-thirds-absolute.md`.

**The axioms, re-run here** (not taken from `vendor/zeta23/AUDIT.md`): `Zeta23.thmA₀`,
`thmA₀_cumulative`, `thmB₀`, `thmC₀`, `thmA₀_N0` and this repository's
`two_thirds_on_critical_line` each print exactly `[propext, Classical.choice, Quot.sound]`.
`thmA₀` is `thmA₁ zetaEF` and `zetaEF : EF.EF_lit zetaZeroConfig` is a theorem, so Theorem A has no
hypotheses.  This is now permanent: the exhaustive audit of §2 runs through the vendored proofs in
the dependency closure of every result this repository derives from them.

**The statements, read against Mathlib.**  `zerosIn T₁ T₂` is
`{ρ | riemannZeta ρ = 0 ∧ 0 < ρ.re ∧ ρ.re < 1 ∧ T₁ < ρ.im ∧ ρ.im ≤ T₂}` and `zeroMult ρ` is
`(analyticOrderAt riemannZeta ρ).toNat`.  `Ncount` sums multiplicities over that set; `N0star` is
the `ncard` of its on-line part.  So the normalization is the literature's, and the asymmetry runs
the strong way: multiplicity on the left, distinct points on the right.

**The denominator is not empty** — this is the check that reading definitions cannot give, and the
new module `RiemannHypothesis/Zeta23Verification.lean` supplies it.  From the vendored (also
unconditional) Riemann–von Mangoldt formula:

* `windowCount_sub_mainTerm_le`: `|N(T,2T) − (T/2π)(log(T/2π) + 2log 2 − 1)| ≤ C log T` for large
  `T` — the main term is exactly the classical `N(2T) − N(T)`, so `windowCount` *is* `N`;
* `eventually_windowCount_ge`: hence `N(T,2T) ≥ (T/4π) log T`;
* `eventually_windowCountOnLine_ge`: hence, for all large `T`, at least `(T/8π)·log T` **distinct**
  zeroes of `ζ` on the critical line with ordinate in `(T, 2T]`;
* `eventually_windowCountSimpleOnLine_ge`: as many **simple** ones, from Theorem B.

So the result is a real result about Mathlib's `ζ`, with the literature's normalization, and with
content that survives being stated without any ratio.  What this does *not* do is re-prove the
vendored analytic argument; for that, the comparator route in `vendor/zeta23/AUDIT.md` remains the
independent check.

## 3. Is the conditional-theorem classification exhaustive?

The mechanism was sound in outline but had four blind spots.  All four are now closed in
`scripts/conditional_theorems.lean`:

1. only `Prop`-valued `def`s counted as statements, so a `Prop`-valued **structure, class or
   inductive** used as a hypothesis was invisible;
2. only *this repository's* statements were scanned, so a hypothesis taken from the vendored
   library (`PaperInputs`, `EF_lit`, `RiemannVonMangoldt`, …) was invisible;
3. Mathlib's own `RiemannHypothesis` — for which this repository's `ZetaForm` is an `abbrev` — was
   invisible, so a theorem stated directly against it would not have been reported;
4. a statement was treated as discharged whenever *any* proof with the same head constant existed,
   so `P a` could be cleared by a proof of `P b`.  Dischargedness is now tested against the exact
   proposition, arguments included; the head test survives only where the hypothesis still has
   loose bound variables, which is the `∀ Z, P Z → …` shape, i.e. the `DEFINITIONAL` case.

**Result: the output is unchanged.**  The recorded 36 conditional theorems, in the same three
classes, with no `UNCLASSIFIED` entry, is what the strengthened detector reports too — so the
classification was in fact exhaustive.  Positive controls confirm the new powers are real: probe
theorems assuming `_root_.RiemannHypothesis`, and assuming a parameterized statement at an argument
for which no proof exists, are both reported now and were both invisible before.

(The list has since grown by three entries, from the new module of §5, all of the expected kind:
theorems whose hypothesis *is* the Riemann hypothesis.)

## 5. The attempt at the conjecture itself

The Riemann hypothesis is open and nothing here proves it; the corpus ceiling already proved in
`RiemannHypothesis/CorpusCeiling.lean` says the present route cannot pass 67 %.  What can be done
honestly is to pin down *exactly* what is missing, and one piece of the received answer turns out
to be wrong.

`RiemannHypothesis/EventualCountingCriterion.lean`:

* `zetaStripForm_of_eventually_windowCountOnLine_eq` — if `N₀*(0,T) = N_d(0,T)` for all
  **sufficiently large** `T`, the Riemann hypothesis follows.  No verification of the low zeroes is
  needed, contrary to the natural guess: an off-line zero can be taken with positive ordinate
  (`ζ` has no real zero in `(0,1)`, and the zero set is closed under conjugation), and it is then
  missed by *every* window `(0, T]` above it, so the deficiency is permanent.
* `zetaStripForm_iff_eventually_windowCountOnLine_eq`, and the same criterion in the multiplicity
  count `zetaStripForm_iff_eventually_windowCountOnLine_eq_windowCount` (the exact denominator the
  two-thirds theorem bounds; this form also forces simplicity), and
  `zetaStripForm_iff_eventually_windowCountDistinct_le`, which exhibits the conjecture as the
  endpoint `c = 1` of the family `(c − ε)·N ≤ N₀*` of which `c = 2/3` is proved.

This is a reduction, not progress on the conjecture: its hypothesis is as hard as the conjecture.
What it settles is the shape of the remaining work — entirely asymptotic, with no finite check
attached.

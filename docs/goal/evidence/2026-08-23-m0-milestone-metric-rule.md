# M0-MILESTONE-METRIC-RULE — hypothesis hygiene, and milestones that name a theorem

Date: 2026-08-23.

## What changed

`AGENTS.md` gained three sections, and `scripts/audit.sh` a sixth check.

1. **Hypothesis hygiene.**  Before any Lean work on a route that introduces an *assumed*
   `def ... : Prop`, four questions must be answered in writing, in the module docstring and
   in the task-board row:

   * *Direction* — which inequality is free unconditionally, and is it the one the route needs
     or its reverse?
   * *Strength* — does the hypothesis already imply the target?
   * *Non-triviality* — is there any proof of it other than `RH ⟹ P`?
   * *Attribution* — which object is the cited classical theorem actually about?

2. **Milestones name a classical theorem, not a percentage.**

3. **The conditional/unconditional boundary is machine-checked**, by
   `scripts/conditional_theorems.lean` against `docs/goal/conditional-theorems.txt`.

## Why these four questions

Each is a question the withdrawn `SpeiserTransfer` / `SpeiserOffLineTransfer` route failed,
and each was answerable on the first day of that route, before any Lean work:

* *Direction*: the free inequality is
  `xiDerivWindowCountOffLineMult_le_windowCountOffLineMult` — Rolle's theorem for Hardy's `Ξ`
  gives `ξ′` **at most** as many off-line zeroes as `ζ`, which is the reverse of what the
  route assumed.  Rolle's theorem is elementary; it was formalized last (`M1-SPEISER-ROLLE`),
  not first.
* *Strength*: `eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer` shows the
  hypothesis yields `86.864 %` on the critical line, while the row's target was `80 %`.
* *Non-triviality*: the only proof of the hypothesis in the repository is
  `speiserOffLineTransfer_of_zetaStripForm` — from the Riemann hypothesis itself.
* *Attribution*: the hypothesis was labelled "the counting form of Speiser's theorem
  (Levinson–Montgomery)".  Levinson–Montgomery counts the zeroes of `ζ′`; the `Prop` is about
  the zeroes of `ξ′`.

## Why the percentage is retired as a metric

The vendored mollifier machinery has a bandwidth-one ceiling of about `0.6818`
(`M1-SIXTY-SEVEN-CRITICAL`, `M1-EIGHTY-CRITICAL-ROUTE`).  Re-deriving or repackaging results
already in the repository therefore cannot move the **unconditional** proportion of zeroes on
the critical line past that ceiling; only new mollifier mathematics (`M2-MOLLIFIER`) could,
and that is research rather than formalization.  A percentage target also fails to separate a
conditional theorem from an unconditional one — three days of work produced only theorems
with hypotheses while the unconditional proportion stayed at `2/3` (`0.6725…` with the optimal
window).  A milestone phrased as "prove Bohr–Landau" or "prove a density theorem" is decided
by reading a statement.

## Commands

```bash
python3 scripts/goal_state.py validate
```

## Adversarial revalidation: M0-MILESTONE-METRIC-RULE

Re-checked independently of the first pass:

* **Claim mode.**  This row is a *governance* row: it changes documentation and adds a check
  script.  It proves no mathematics and claims none.  Nothing in it asserts that the Riemann
  hypothesis, Speiser's theorem, or any proportion result holds.
* **Every constant checked by hand.**  `0.6818` and `0.6725…` are quoted from the existing
  rows `M1-SIXTY-SEVEN-CRITICAL` and `M1-EIGHTY-CRITICAL-ROUTE`, not recomputed here, and are
  described as the ceiling *of the machinery as formalized*, which is what those rows record.
  `86.864 %` and `80 %` are the constants appearing verbatim in
  `eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer` and in the exit
  criteria of `M1-EIGHTY-CRITICAL-ROUTE`.
* **The four precedents are real declarations.**  `xiDerivWindowCountOffLineMult_le_windowCountOffLineMult`,
  `eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer` and
  `speiserOffLineTransfer_of_zetaStripForm` all exist in the library and are pinned in
  `scripts/revalidation.lean`; the Levinson–Montgomery attribution was withdrawn in
  `M1-SPEISER-ROLLE` and is now also corrected in `README.md`.
* **The new check is load-bearing and falsifiable.**  Deleting a line from
  `docs/goal/conditional-theorems.txt`, or adding a theorem with an unproved `Prop` in its
  hypotheses without updating the manifest, makes `./scripts/audit.sh` fail at step 6.
* **No vacuity.**  The manifest is non-empty: the conditional theorems of
  `EightyPercentRoute.lean`, `EightyPercentMultiplicity.lean`, `SpeiserMultiple.lean`,
  `Partial.lean` and the criterion files are listed there by name.

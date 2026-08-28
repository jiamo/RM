# AGENTS.md

This file is for humans and coding agents working in this repository.

## Repository purpose

Formalize the **Riemann hypothesis** in Lean: its precise statement, the equivalence
of its standard formulations, and — as the long-term goal tracked on the task board
— a proof. The Riemann hypothesis is open; the repository proves equivalences and
prerequisites, states the conjecture and the known partial results as `Prop`, and
tracks the proof attempt on the task board. See `README.md` and
`docs/goal/goal-prompt.md`.

## Startup Route

1. Read `docs/goal/goal-prompt.md` for the execution protocol and claim hygiene.
2. Read `docs/current-goal-state.md` for the active summarized task state.
3. Inspect `docs/goal/task-board.yaml` through `python3 scripts/goal_state.py next`
   before choosing follow-up work.
4. Validate task-board edits with `python3 scripts/goal_state.py validate`.

## Task Board Rule

`docs/goal/task-board.yaml` is the machine-readable task queue for this repository.

- New actionable work should be normalized into the task board instead of being
  left only in chat.
- `DONE_STRONG` means the listed exit criteria are proven and `open_boundary` is
  empty; for the Riemann hypothesis itself that means a Lean-checked proof term.
- `DONE_WEAK` remains unfinished.

## Commands

```bash
python3 scripts/goal_state.py validate
python3 scripts/goal_state.py next
python3 scripts/goal_state.py render   # writes docs/current-goal-state.md
lake build
./scripts/audit.sh
```

## Hypothesis hygiene (run this before opening a new route)

Whenever a route introduces a new `def ... : Prop` that is *assumed* rather than proved
— a "transfer", an "input", a "classical theorem we have not formalized" — answer these
four questions **in writing, in the module docstring and in the task-board row**, before
any Lean work on the route begins.  It costs minutes; skipping it has cost days.

1. **Direction.**  Which inequality is free, unconditionally, and is it the one you need
   or its reverse?  Write both down side by side.  If the free one is the reverse, then
   the missing half is the whole problem, and it should be attacked, or recorded, first.
   *Precedent:* Rolle's theorem for Hardy's `Ξ` gives exactly the reverse of
   `SpeiserOffLineTransfer`, and Rolle is elementary — it could have been done on day one.
2. **Strength.**  Does the hypothesis already imply the target?  Compute what it yields
   before building on it.  If it yields `86.864 %` while the target is `80 %`, then the
   hypothesis is stronger than the conclusion and the route assumes its own conclusion.
   *Precedent:* `eighty_six_percent_on_critical_line_mult_of_speiserOffLineTransfer`.
3. **Non-triviality.**  Is there any proof of the hypothesis other than `RH ⟹ P`?  If the
   only one available is from the conjecture itself (as in
   `speiserOffLineTransfer_of_zetaStripForm`), there is no evidence that `P` is weaker
   than `RH`, and a theorem `P → Q` is not progress towards `Q`.
4. **Attribution.**  When a hypothesis is labelled with a classical theorem, check which
   object that theorem is about.  Levinson–Montgomery counts the zeroes of `ζ′`; the
   `Prop` here was about `ξ′`.  One character apart, and the citation was simply wrong.
   Cite the statement, not the slogan, and name the object it quantifies over.

A route that cannot answer all four is not ready to be worked on.  Prefer, in this order:
an unconditional theorem; a hypothesis strictly weaker than the target with a proof that
does not pass through the conjecture; a hypothesis recorded as open with all four answers
written down.

## Milestones are named theorems, not percentages

Do not use a numerical proportion of zeroes on the critical line as a milestone target.
The mollifier machinery formalized here has a bandwidth ceiling near `0.6818`, so no
repackaging of existing results moves the *unconditional* proportion past it; only new
mollifier mathematics (`M2-MOLLIFIER`) would, and that is research, not formalization.
Phrase milestones as "prove classical theorem X" — Bohr–Landau, a density theorem, the
argument principle on rectangles.  Whether such a row advanced is decidable by reading a
statement; whether "the percentage moved" is not, once conditional theorems are in play.

## Conditional versus unconditional is machine-checked

`./scripts/audit.sh` runs `scripts/conditional_theorems.lean`, which lists every theorem
of the library that takes an *unproved* `Prop` of this repository as a hypothesis, and
diffs the list against `docs/goal/conditional-theorems.txt`.  Adding or removing a
conditional theorem therefore requires updating that manifest in the same commit; the
boundary does not rest on docstring discipline.  Regenerate with

```bash
lake env lean scripts/conditional_theorems.lean > docs/goal/conditional-theorems.txt
```

## Claim hygiene (short form)

- A `def ... : Prop` is a statement, not a proof. `ZetaForm` and the entries of
  `RiemannHypothesis/Partial.lean` are statements.
- `sorry` is allowed only in `Challenge.lean`.
- Never report a statement as a proof, or a mathlib theorem as proved here.

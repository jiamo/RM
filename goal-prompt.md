# Riemann hypothesis goal execution protocol

This is the single, stable, agent-neutral protocol for active goal work in this
repository. The goal is to **prove the Riemann hypothesis in Lean** — to construct,
in this repository, a term of type `RiemannHypothesis.ZetaForm` that Lean accepts.

The Riemann hypothesis is open. This protocol therefore has two honest consequences
that the status vocabulary below encodes:

* the board's dependency graph does **not** pretend that the conjecture is reachable
  from the known partial results — the chain must pass through the research row
  `M3-GAP`, which has no known route;
* a row is `DONE_STRONG` only when **Lean checks a proof** — a literature claim, a
  mathlib theorem, and a `Prop` statement are all weaker forms of evidence and are
  labelled as such.

## Objective

Continue selecting and completing task-board rows until every row is `DONE_STRONG`
or a real external blocker prevents further progress. `DONE_WEAK` is unfinished.
No other document may own an executable task list.

## 0. Authority and execution

Read `AGENTS.md`, this file, `docs/current-goal-state.md`, and
`docs/goal/task-board.yaml` in that order. The structured task board is the only
executable queue. A new actionable human request must be normalized into a row
before task selection.

Run:

```bash
python3 scripts/goal_state.py validate
python3 scripts/goal_state.py next
```

Selection is milestone- and dependency-aware. `DONE_WEAK` remains unfinished.
Use `DONE_STRONG` only when every listed exit criterion is proven, every required
gate has a final successful result, `open_boundary` is empty, and a small evidence
file is linked from the row.

### 0.1 Status vocabulary

- `DISCOVERED`: observed but not yet shaped into an executable card.
- `TODO_NEEDS_DESIGN`: claim boundary or mechanism is not yet coherent.
- `TODO_READY`: finite, dependency-ready implementation work.
- `IN_PROGRESS`: implementation is active.
- `TESTING`: implementation exists; required evidence is still running.
- `DONE_WEAK`: a real slice passed, but the card's full boundary remains open.
- `DONE_STRONG`: the full finite card is proven with no open boundary.
- `BLOCKED`: use only after the repository's repeated-blocker threshold.
- `CLAIM_RISK`: useful evidence exists but cannot support the broad claim implied
  by the task title.

### 0.2 Evidence

Each completed slice gets one file under `docs/goal/evidence/` naming the task,
the Lean declarations it adds or changes, the exact commands run, the observed
output, the supported claim, and what is not proven. A build log without a final
`lake build` success and `./scripts/audit.sh` pass is not green. Do not rewrite
authoritative baselines to absorb a regression.

### 0.3 Claim hygiene

Every claim must label all relevant modes:

```text
statement (a def of Prop) vs proof (a theorem)
formulation equivalence vs the conjecture itself
provided by mathlib vs proved in this repository
informal literature claim vs Lean-checked proof
```

In particular:

- `RiemannHypothesis.ZetaForm`, `ZetaStripForm`, `EtaForm` and every entry of
  `RiemannHypothesis.Partial.lean` are **statements**, not proofs. A row that
  merely states a result is `DONE_STRONG` for *stating* it only if its
  `exit_criteria` say exactly that.
- A theorem that mathlib already provides (for example
  `riemannZeta_ne_zero_of_one_le_re`) is `DONE_STRONG` only with evidence naming
  the mathlib declaration; the exit criterion must say "proved by mathlib's X",
  not "proved here".
- A row is `DONE_STRONG` for the Riemann hypothesis only when a term of type
  `ZetaForm` exists and Lean checks it. No other evidence — numerical, heuristic,
  or literature — can close `M4-RH`.

### 0.4 No closing by reduction to an open conjecture

A row is never `DONE_STRONG` on the strength of a reduction to another unproved
conjecture. Reductions to open conjectures, computational verification through any
fixed parameter, and candidate counterexamples without a proved certificate are
insufficient. Such a row is `DONE_WEAK` at best, and it must carry

```yaml
open_conjecture_reduction: true
```

which `python3 scripts/goal_state.py validate` rejects in combination with
`DONE_STRONG`. The check is syntactic — a tripwire, not a proof — so the flag must
be set honestly when a row's content is a reduction. Note that the *equivalence of
formulations* of the same conjecture (`M0-EQUIV`) is not a reduction to another
conjecture: it proves an `Iff` between statements and asserts neither side.

### 0.5 Adversarial revalidation of closed rows

A row does not close on a status report. Every `DONE_STRONG` row needs a second,
adversarial pass, recorded in the file named by its `revalidation:` field under a
heading

```text
## Adversarial revalidation: <task id>
```

and `python3 scripts/goal_state.py validate` fails when that section is missing.
The pass re-checks, independently of the first: every claimed constant against a
value computable by hand; every hypothesis for vacuity and for being load-bearing;
the claim mode (statement vs proof, mathlib vs proved here); and the exact
statement of each declaration, through the statement pinning in
`scripts/revalidation.lean`, where the claim is written out in full and the
repository's declaration is supplied as the proof term. A renamed or weakened
declaration then stops that file from elaborating, and `./scripts/audit.sh` fails.

## 1. North star

The Riemann hypothesis: every nontrivial zero of the Riemann zeta function has
real part `1/2`. In this repository the statement of record is
`RiemannHypothesis.ZetaForm` (equivalent, by `RiemannHypothesis.Main`, to the
strip form and to the Dirichlet-eta form). The north-star row is `M4-RH`; it
depends on `M3-GAP`, the research row, because no known result implies the
conjecture. Proving any of the partial results in M1–M2 is valuable checked
landmark work and builds the analytic-number-theory infrastructure, but it does
not by itself move the north star.

## 2. Work loop

For one selected card:

1. Read routed investigations and design documents.
2. Reproduce the smallest failing boundary; compare with the informal statement.
3. Add a focused lemma before changing shared declarations.
4. Implement one coherent proposal; do not stack unverified speculative edits.
5. Run focused gates, then the card's adjacent gates as required by the changed
   boundary.
6. Record evidence, update the row, validate the board, and regenerate
   `docs/current-goal-state.md`.
7. Hard rows (any row whose `open_boundary` mentions "no known route" or whose
   prerequisites are absent from mathlib) are attacked with at least two independent
   strategies, and a separate adversarial pass re-checks every claimed constant and hidden
   assumption before the row may be marked `DONE_STRONG`. Status reports and "routine"
   claims are rejected. (Rule adopted from the Crouzeix-conjecture agent conversation;
   see `references/README.md`.)

### 2.1 Chained delivery of ready rows

By default one delivery completes one selected card. As an exception, rows that
form a single dependency chain (each row's `depends_on` contains the previous row)
and that are **all** `TODO_READY` when the delivery starts may be completed in one
delivery, in dependency order, subject to all of the following:

1. Every row in the chain keeps its own evidence file, its own exit criteria,
   and its own adversarial revalidation (§0.2, §0.5); batching never merges or
   weakens per-row evidence.
2. The repository gates (`lake build`, `./scripts/audit.sh`) and
   `python3 scripts/goal_state.py validate` pass after **each** row, not only at
   the end of the chain.
3. The chain stops at the first row that cannot reach `DONE_STRONG`; that row is
   recorded honestly (`DONE_WEAK`, `BLOCKED`, `CLAIM_RISK`, …) and no later row of
   the chain is started in the same delivery.
4. A row that is `TODO_NEEDS_DESIGN`, `DISCOVERED`, or a research row (for example
   `M3-GAP`) is never part of a chain, and a chain never crosses into one.
5. A second instance of a shared mechanism (for example a second application of
   a bridge built earlier in the chain) may be appended to the chain only if its
   row is itself `TODO_READY` and depends on the row that built the mechanism.

All shell commands require explicit timeouts. Never commit unless the user asks.
Never discard shared worktree changes.

## 3. Active milestone order

The durable order is encoded in the board:

```text
M0 statement, equivalence, and foundations        (done)
M1 classical results, 1896–1914 (PNT, zero-free region, Hardy, Bohr–Landau)
M2 modern partial results, 1942–1989 (Selberg, Levinson, Conrey, density)
M3 research: the step beyond the known results
M4 the Riemann hypothesis itself
```

## 4. Gate ownership

`lake build` and `./scripts/audit.sh` are the repository-wide gates. A row may
add focused gates (e.g. building a specific module) but may not weaken the
repository gates. `./scripts/audit.sh` checks that `sorry` appears only in
`Challenge.lean` and that the compared theorems depend only on `propext`,
`Quot.sound` and `Classical.choice`.

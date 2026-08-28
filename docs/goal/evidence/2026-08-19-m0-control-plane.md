# M0-GOAL-CONTROL-PLANE evidence

Task: make goal selection milestone-aware, dependency-aware, and order-independent.

Source identity: `docs/goal/goal-prompt.md`, `docs/goal/task-board.yaml`,
`scripts/goal_state.py` (modelled on the pcc project's task board).

Changed behavior:

- `docs/goal/task-board.yaml` is the only executable task queue: 24 rows across
  milestones M0 (statement/equivalence/foundations), M1 (classical results),
  M2 (modern partial results), M3 (research), M4 (the conjecture).
- `scripts/goal_state.py` validates the board (unique ids, known statuses and
  priorities, known dependencies, no later-milestone dependencies, no dependency
  cycles), selects the next dependency-ready task in the active milestone, and
  renders `docs/current-goal-state.md`.

Commands run:

```bash
python3 scripts/goal_state.py validate
python3 scripts/goal_state.py next
python3 scripts/goal_state.py render
lake build
./scripts/audit.sh
```

Observed results:

- `validate`: "OK: 24 tasks validate".
- `next`: selects `M1-GROWTH` (P0, TODO_READY, dependency `M0-EQUIV` which is
  DONE_STRONG).
- `render`: wrote `docs/current-goal-state.md`.
- `lake build`: zero errors; `audit.sh`: OK.

Supported claim: the board is the executable queue; selection is milestone- and
dependency-aware; M0 rows are closed; the active milestone is M1.

Not proven: any mathematics beyond the M0 rows; the board's dependency graph does
not imply the Riemann hypothesis is reachable (the chain must pass through the
research row M3-GAP, which has no known route).

# OpenAI family 003 intake — 2026-10-11

This is an intake and delegation record, not evidence of a proved theorem.

User-authorized destination: https://aristotle.harmonic.fun/projects/2f796a67-1713-496c-a3b8-1b42278e9c5a
Local work is confined to `/Users/jiamo/projects/riemman` and temporary source caches.
No files or proof terms in church-turing are modified.

## Fixed source and scope

- Repository: https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
- Latest main checked on 2026-10-11: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` (2026-10-08 update).
- Official result scope: [family 003](https://github.com/openai/math/blob/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/lean/docs/003.md).
- Registered targets: zeta, Dirichlet and Eisenstein finite-order Hecke nonvanishing for Re(s) > 7/8, and a uniform logarithmic real-zero gap for primitive nonprincipal real Dirichlet characters.
- The October 5 paper concerns an alternate 11/12 bound; it is included as reference, not claimed as a separately registered Lean proof.
- These results do not state the Riemann hypothesis. The existing RH statement remains a statement until its own proof is checked.

## Completeness and compatibility

- 3232 OAI Lean modules in the four registered entrypoints' static transitive import closure.
- 31 additional Lean modules in the closure from PrimeNumberTheoremAnd and rellich-kondrachov, at fixed revisions with the upstream compatibility patches applied to reference copies. Licenses, manifests and patches are included.
- All other imports resolve to the Mathlib/Lean standard environment; no unresolved nonstandard imports in the static inventory.
- All three associated paper directories (PDF and TeX), comparator specifications, source catalog, licenses and build metadata are included.
- No local private-project source is uploaded. Automatic approval rejected the initial proposal to attach a complete host snapshot; the final transport contains only public upstream source, public dependencies and the user-authorized task instructions. Aristotle must use its existing project code as the host baseline.
- Every file has a SHA-256 digest. The restorer verifies all files and rejects unsafe paths or conflicting overwrites.
- Host stays on Lean 4.33.0 / Mathlib db584cd6. Upstream used Lean 4.34.1 / Mathlib d13f23b7. No local build or audit was run; Aristotle is instructed to adapt and validate there.

## Dispatch

Payload and prompt: `.aristotle/openai-rh-fd4aeeb/` (ignored; contains no API key).
The four new M1 task-board rows retain their mathematical exit criteria. Upload alone cannot close them.
Submission status: WAITING_FOR_CAPACITY. The first public-only API attempt was explicitly rejected with HTTP 429 (account concurrency limit); target remained IDLE with no new task. A one-shot sender will wait up to 24 hours for capacity without cancelling any existing task. The acknowledged task identity will be appended by the sender. This is not yet a successful dispatch or proof absorption.

Acknowledged dispatch: https://aristotle.harmonic.fun/projects/2f796a67-1713-496c-a3b8-1b42278e9c5a?task=df14353a-a7d4-481c-aeb7-51f78e4a55ab
Task status at receipt: QUEUED. This confirms task acceptance, not proof absorption.

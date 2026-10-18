# Brun–Titchmarsh with the constant `2 + ε`

Date: 2026-10-18
Task: `M2-BRUN-TITCHMARSH-TWO` (new, `DONE_STRONG`)
Module: `RiemannHypothesis/BrunTitchmarshTwo.lean` (new; imports `BrunTitchmarshSharp` and
`LargeSieveMV`)

## Claim

```lean
theorem large_sieve_farey_mv {s : Finset ℚ} {Q : ℕ} (hQ : 2 ≤ Q)
    (hmem : ∀ x ∈ s, x ∈ Set.Ico (0 : ℚ) 1) (hden : ∀ x ∈ s, x.den ≤ Q)
    (a : ℕ → ℂ) (N : ℕ) :
    ∑ x ∈ s, ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * (x : ℝ))‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + N) * ∑ n ∈ range N, ‖a n‖ ^ 2

theorem large_sieve_farey_pairs_mv {Q : ℕ} (hQ : 2 ≤ Q) (a : ℕ → ℂ) (N : ℕ) :
    ∑ q ∈ Icc 1 Q, ∑ b ∈ (range q).filter (fun b => Nat.Coprime b q),
        ‖∑ n ∈ range N, a n * e2pi ((n : ℝ) * ((b : ℝ) / (q : ℝ)))‖ ^ 2
      ≤ ((Q : ℝ) ^ 2 + N) * ∑ n ∈ range N, ‖a n‖ ^ 2

theorem card_le_sifted_squarefree_mv {N Q : ℕ} (hQ : 2 ≤ Q) {A : Finset ℕ} (hA : A ⊆ range N)
    (w : ℕ → ℕ) (hwpos : ∀ p, p.Prime → p ≤ Q → 0 < w p) (hwle : ∀ p, p.Prime → p ≤ Q → w p ≤ p)
    (hAw : ∀ p, p.Prime → p ≤ Q → (A.image (fun n => n % p)).card ≤ w p) :
    (A.card : ℝ) * ∑ q ∈ squarefreeUpTo Q, ∏ p ∈ q.primeFactors, (((p : ℝ) - w p) / w p)
      ≤ (Q : ℝ) ^ 2 + N

theorem card_primes_Ico_le_of_level_mv (x y : ℕ) {Q : ℕ} (hQ : 2 ≤ Q) :
    (((Ico x (x + y)).filter Nat.Prime).card : ℝ)
      ≤ ((Q : ℝ) ^ 2 + y) / Real.log Q + Q + 1

theorem card_primes_Ico_le_two {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℕ, ∀ y : ℕ, Y ≤ y → ∀ x : ℕ,
      (((Ico x (x + y)).filter Nat.Prime).card : ℝ)
        ≤ (2 + eps) * y / Real.log y

theorem card_primes_Ico_mod_le_two {eps : ℝ} (heps : 0 < eps) :
    ∃ Y₀ : ℕ, ∀ q a : ℕ, 1 ≤ q → a < q → ∀ x y : ℕ, Y₀ ≤ y / q + 1 →
      (((Ico x (x + y)).filter (fun n => n.Prime ∧ n % q = a)).card : ℝ)
        ≤ (2 + eps) * ((q : ℝ) / (q.totient : ℝ)) * ((y / q + 1 : ℕ) : ℝ)
            / Real.log ((y / q + 1 : ℕ) : ℝ)

theorem card_primes_range_le_two {eps : ℝ} (heps : 0 < eps) :
    ∃ Y : ℕ, ∀ N : ℕ, Y ≤ N →
      (((range N).filter Nat.Prime).card : ℝ) ≤ (2 + eps) * N / Real.log N
```

All in namespace `RiemannHypothesis.BrunTitchmarshTwo`. Each statement is the statement of an
existing theorem with the factor `π` removed:

| new | existing (unchanged) | constant before → after |
| --- | --- | --- |
| `large_sieve_farey_mv` | `LargeSieveFarey.large_sieve_farey` | `Q² + πN` → `Q² + N` |
| `large_sieve_farey_pairs_mv` | `LargeSieveFarey.large_sieve_farey_pairs` | `Q² + πN` → `Q² + N` |
| `card_le_sifted_squarefree_mv` | `LargeSieveSquarefree.card_le_sifted_squarefree` | `Q² + πN` → `Q² + N` |
| `card_mul_siftSum_le_mv` | `BrunTitchmarsh.card_mul_siftSum_le` | `Q² + πN` → `Q² + N` |
| `card_mul_siftSumCoprime_le_mv` | `BrunTitchmarsh.card_mul_siftSumCoprime_le` | `Q² + πN` → `Q² + N` |
| `card_primes_Ico_le_of_level_mv` | `BrunTitchmarsh.card_primes_Ico_le_of_level` | `(Q² + πy)/log Q + Q + 1` → `(Q² + y)/log Q + Q + 1` |
| `card_primes_Ico_mod_le_of_level_mv` | `BrunTitchmarsh.card_primes_Ico_mod_le_of_level` | `(Q² + πY) q/(φ(q) log Q) + Q + 1` → `(Q² + Y) q/(φ(q) log Q) + Q + 1` |
| `level_bound_le_two` | `BrunTitchmarsh.level_bound_le_two_pi` | `2π + ε` → `2 + ε` |
| `card_primes_Ico_le_two` | `BrunTitchmarsh.card_primes_Ico_le_two_pi` | `(2π + ε) y/log y` → `(2 + ε) y/log y` |
| `card_primes_Ico_mod_le_two` | `BrunTitchmarsh.card_primes_Ico_mod_le_two_pi` | `(2π + ε)(q/φ(q)) Y/log Y` → `(2 + ε)(q/φ(q)) Y/log Y` |
| `card_primes_range_le_two` | `BrunTitchmarsh.card_primes_range_le_two_pi` | `(2π + ε) N/log N` → `(2 + ε) N/log N` |

Mode: a **proof**, in this repository, of Brun–Titchmarsh with the constant `2 + ε` for
`y ≥ Y(ε)`, uniformly in `x`. Montgomery and Vaughan ("The large sieve", Mathematika 20 (1973),
Theorem 2) prove the exact constant `2` for every `y > 1`; that is **not** claimed here.

## Proof

Approach: **duplication**, not refactoring. Every new theorem is a copy of the proof of the
corresponding existing theorem, started from `LargeSieveMV.large_sieve_mv` (constant `N + δ⁻¹`)
instead of `LargeSieveGallagher.large_sieve_gallagher` (constant `δ⁻¹ + πN`). No existing file of
the chain was edited, so every pinned statement and every existing proof is byte-for-byte as it
was. The new module cannot live in `LargeSieveFarey.lean`, because `LargeSieveMV` imports
`LargeSieveDual`, which imports `LargeSieveFarey`.

1. *Farey fractions.* With `δ = Q⁻²` (`inv_sq_le_intDist_sub`), `large_sieve_mv` gives
   `(N + Q²) ∑ ‖a n‖²`, rewritten as `(Q² + N) ∑ ‖a n‖²`. The double-sum form over reduced
   fractions `b/q`, `q ≤ Q`, follows as before (`den_natCast_div`, `mem_Ico_natCast_div`).
2. *Montgomery's sieve.* The lower bound `|A|² ∏_{p | q} (p − w p)/(w p) ≤ ∑_b |S(b/q)|²`
   (`sq_card_mul_prod_le_redSq`, unchanged) summed over squarefree `q ≤ Q`, against step 1.
3. *Brun–Titchmarsh at level `Q`.* The primes of `[x, x + y)` above `Q` avoid the class `0`
   modulo every prime `p ≤ Q` (`shifted_primes_avoid`), so step 2 with `w p = p − 1` gives
   `|A| siftSum Q ≤ Q² + y`, and `log Q ≤ siftSum Q` (`log_le_siftSum`). The primes at most `Q`
   number at most `Q + 1`.
4. *Optimization.* At `Q = ⌊√y / log y⌋`, with `t = log y`: `Q² ≤ y/t²` and
   `log Q ≥ t/2 − log t − 1`, so `(Q² + y)/log Q ≤ (2 + ε/2) y/t` once
   `1/t + t ≤ (2 + ε/2)(t/2 − log t − 1)`, i.e. once `(2 + ε/2)(log t + 1) + 1/t ≤ εt/4`, which
   the chain of `level_bound_le_two_pi` establishes for `t ≥ (1000/ε)² + 10⁶` (the bound
   `2π + ε/2 ≤ 7` used there is replaced by `2 + ε/2 ≤ 7`). `Q + 1 ≤ (ε/2) y/t` as before.
5. *Progressions.* The same with `w p = p` for `p | q`, `siftSumCoprime`, and the factor
   `c = q/φ(q) ≥ 1` carried through step 4.

## Hypothesis hygiene

No new `def … : Prop`, and no theorem with an unproved `Prop` as hypothesis;
`docs/goal/conditional-theorems.txt` is unchanged.

## Adversarial revalidation: M2-BRUN-TITCHMARSH-TWO

* *The constant is the pinned one.* `scripts/revalidation.lean` writes out `(2 + eps) * y /
  Real.log y` and `(2 + eps) * ((q : ℝ) / (q.totient : ℝ)) * …` and supplies
  `card_primes_Ico_le_two` and `card_primes_Ico_mod_le_two`; it also pins
  `large_sieve_farey_mv`, `card_le_sifted_squarefree_mv` and `card_primes_Ico_le_of_level_mv`
  with `Q² + N` and `(Q² + y)/log Q + Q + 1`. Axioms of all nine public theorems are pinned in
  step 3 of `scripts/audit.sh`.
* *No `π` left.* `rg 'Real.pi' RiemannHypothesis/BrunTitchmarshTwo.lean` finds nothing: the
  statements and the proofs contain no `π`.
* *Consistency with known values.* `y = 10⁶`, `x = 0`: there are 78498 primes below `10⁶` and
  `2 y/log y ≈ 144765`, so the bound holds with room, as it must; the prime number theorem
  gives `π(y) ~ y/log y`, so no constant below `1` could hold for `x = 0` — the theorem is
  consistent with that.
* *Vacuity.* `card_primes_Ico_le_two` quantifies over all `y ≥ Y` and all `x`; the threshold `Y`
  is explicit in the proof (`max 3 ⌈exp((1000/ε)² + 10⁶)⌉`), astronomically large but finite.
  There is no hypothesis beyond `0 < ε`.
* *Not the exact 2.* The statement has `2 + eps` with `eps > 0` and a threshold depending on
  `eps`; it does not imply Montgomery–Vaughan's `π(x + y) − π(x) ≤ 2y/log y` for all `y > 1`.
* *Claim mode.* A proof in this repository; no Mathlib sieve result is used.

## Not proved

* Montgomery–Vaughan's exact constant `2` for every `y > 1` (it needs explicit control of the
  lower-order terms, and Selberg's `Q² + N − 1` or an equivalent for small `y`).
* Selberg's constant `Q² + N − 1` for the Farey large sieve, and the character form.
* An effective threshold: `Y(ε)` is not optimized; the effective forms of `M2-BRUN-TITCHMARSH`
  (constants `13` and `9`) are unchanged.
* Anything about `ζ`.

## Commands and gates

R3 was started only after R1 and R2 were closed and gated (see
`2026-10-18-m2-large-sieve-mv.md`). In this checkout `scripts/audit.sh` has mode `100644`, so it
was run as `bash scripts/audit.sh`.

* `lake build RiemannHypothesis.BrunTitchmarshTwo` → `Built RiemannHypothesis.BrunTitchmarshTwo`,
  `Build completed successfully (8764 jobs).` (no warnings in the new module).
* `bash scripts/audit.sh` → exit 0. Final lines:
  ```
  ==> lake build
  Build completed successfully (12513 jobs).
  ==> checking for sorry outside Challenge.lean
  ==> checking axioms of the compared theorems
  ==> exhaustive axiom audit (scripts/axiom_audit.lean)
  AXIOM AUDIT: 32123 theorems checked, 0 outside the standard three
  OK
  ==> coverage of the pinned axiom checks (scripts/audit_coverage.py)
  ==> checking for Float
  ==> pinning the claims of the closed rows (scripts/revalidation.lean)
  ==> checking the conditional/unconditional boundary
  ==> validating the task board
  OK: 181 tasks validate
  OK
  ```
* `lake build` (afterwards, standalone) → `Build completed successfully (12513 jobs).`
* `python3 scripts/goal_state.py validate` → `OK: 181 tasks validate`.
* `git diff` of `docs/goal/conditional-theorems.txt` against the start of the round: empty.
* `#print axioms`, from step 3 of the audit run: each of `large_sieve_farey_mv`,
  `large_sieve_farey_pairs_mv`, `card_le_sifted_squarefree_mv`,
  `card_primes_Ico_le_of_level_mv`, `level_bound_le_two`, `card_primes_Ico_le_two`,
  `card_primes_Ico_mod_le_of_level_mv`, `card_primes_Ico_mod_le_two`, `card_primes_range_le_two`
  (namespace `RiemannHypothesis.BrunTitchmarshTwo`) depends on axioms
  `[propext, Classical.choice, Quot.sound]`.

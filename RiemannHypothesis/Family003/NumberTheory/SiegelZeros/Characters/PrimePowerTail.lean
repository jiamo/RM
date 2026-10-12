/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Characters/PrimePowerTail.lean
  Original module: OAI.NumberTheory.SiegelZeros.Characters.PrimePowerTail
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Tactic.Linarith

namespace RiemannHypothesis.Family003

namespace SiegelZeros

section

namespace W55

open scoped BigOperators
open ArithmeticFunction

noncomputable def higherPrimePowerTerm (n : ℕ) : ℝ :=
  (if n.Prime then 0 else vonMangoldt n) / (n : ℝ)

lemma higherPrimePowerTerm_nonneg (n : ℕ) : 0 ≤ higherPrimePowerTerm n := by
  unfold higherPrimePowerTerm
  positivity [vonMangoldt_nonneg (n := n)]

theorem summable_higherPrimePowerTerm : Summable higherPrimePowerTerm := by
  have h := vonMangoldt.summable_residueClass_non_primes_div (0 : ZMod 1)
  convert (preTransparency := .instances) h using 1
  funext n
  simp [higherPrimePowerTerm, vonMangoldt.residueClass,
    show (n : ZMod 1) = 0 from Subsingleton.elim _ _]

noncomputable def higherPrimePowerConstant : ℝ := ∑' n, higherPrimePowerTerm n

lemma higherPrimePowerConstant_nonneg : 0 ≤ higherPrimePowerConstant :=
  tsum_nonneg higherPrimePowerTerm_nonneg

theorem higherPrimePower_sum_le (s : Finset ℕ) :
    (∑ n ∈ s, higherPrimePowerTerm n) ≤ higherPrimePowerConstant :=
  summable_higherPrimePowerTerm.sum_le_tsum s (fun n _ => higherPrimePowerTerm_nonneg n)

theorem vonMangoldt_mass_split (s : Finset ℕ) :
    (∑ n ∈ s, vonMangoldt n / (n : ℝ)) =
      (∑ p ∈ s.filter Nat.Prime, Real.log p / (p : ℝ)) +
      ∑ n ∈ s, higherPrimePowerTerm n := by
  classical
  rw [Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime
  · simp [higherPrimePowerTerm, hp, vonMangoldt_apply_prime hp]
  · simp [higherPrimePowerTerm, hp]

theorem prime_mass_lower_of_vonMangoldt_mass_lower
    (s : Finset ℕ) (L : ℝ)
    (hL : L ≤ ∑ n ∈ s, vonMangoldt n / (n : ℝ)) :
    L - higherPrimePowerConstant ≤
      ∑ p ∈ s.filter Nat.Prime, Real.log p / (p : ℝ) := by
  have htail := higherPrimePower_sum_le s
  rw [vonMangoldt_mass_split] at hL
  linarith

end W55

end

end SiegelZeros

end RiemannHypothesis.Family003

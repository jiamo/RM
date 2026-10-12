/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Reflection/AnnularExponent.lean
  Original module: OAI.NumberTheory.DirichletL.Reflection.AnnularExponent
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - tactic config: 'convert'/'convert_to' run with (preTransparency := .instances), emulating the upstream Lean v4.34 reducibility of instances
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Reflection.ThresholdError

namespace RiemannHypothesis.Family003

namespace SevenEighths.InverseReflectedPhase
open InverseReflectedNormalization InverseKernelSourceUniform
noncomputable section
variable {φ : Type*} [Fintype φ]

theorem physical_scalar_hybrid_shape (F : PrimeFamily φ) (jF : φ→ℕ) (e : φ→Fin 3)
    (Z r Qn Qb kn kb R A C X L ε : ℝ)
    (hZ : 1<Z) (hr : 0<r) (hn : 0<Qn) (hb : 0<Qb) (hkn : 0<kn) (hkb : 0<kb)
    (hR : 0<R) (hC : 0≤C) (hX : 0<X) (hL : 0<L) :
    let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
    let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
    (A/(r*Real.sqrt Qn*Qb)*smallScalar R)^2 * (frozenBranchScale F jF e)^2 *
      (C*(X*U*B*L)^ε*(X+U*B)*B*(U+L+(U*L)^(2/3:ℝ))) ≤
      (A*Real.sqrt kn*kb)^2*(6*C)*Z^(
        InverseTerminalWidths.reflectedExponent 0 (Real.logb Z X)
          (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
          (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
          (Real.logb Z L) (Real.logb Z U) (Real.logb Z B) (3*Real.logb Z r)
          (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) +
        ε*(Real.logb Z X+Real.logb Z U+Real.logb Z B+Real.logb Z L)) := by
  let U := kn*Qn/Ideal.absNorm (frozenExtracted F jF e 1)
  let B := kb*Qb/Ideal.absNorm (frozenExtracted F jF e 2)
  have hp (v : Fin 3) : (0:ℝ)<Ideal.absNorm (frozenExtracted F jF e v) := by
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr (frozenExtracted_ne_zero F jF e v))
  have hU : 0<U := div_pos (mul_pos hkn hn) (hp 1)
  have hB : 0<B := div_pos (mul_pos hkb hb) (hp 2)
  have hs := physical_scalar_extracted F jF e r Qn Qb kn kb R A hr hn hb hkn hkb
  have he := extractedOutsideScalar_log_widths F jF e Z r U B R hZ hr hU hB hR
  have hz0 : 0<Z := lt_trans zero_lt_one hZ
  have hpow (Q : ℝ) (hQ : 0<Q) : Z^(Real.logb Z Q)=Q := Real.rpow_logb hz0 (ne_of_gt hZ) hQ
  have hh := normalized_hybrid_shape hZ.le (Real.logb Z X) (Real.logb Z U) (Real.logb Z B)
    (3*Real.logb Z r) (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 0))
    (InverseTerminalWidths.normWidth Z (frozenExtracted F jF e 2))
    (Real.logb Z U+3*Real.logb Z B+3*Real.logb Z r-Real.logb Z R) (Real.logb Z L) ε
  rw [hpow X hX,hpow U hU,hpow B hB,hpow L hL,← he] at hh
  have hbnd := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh hC)
    (sq_nonneg (A*Real.sqrt kn*kb))
  dsimp only
  rw [hs]
  convert (preTransparency := .instances) hbnd using 1 <;> ring

end
end SevenEighths.InverseReflectedPhase

end RiemannHypothesis.Family003

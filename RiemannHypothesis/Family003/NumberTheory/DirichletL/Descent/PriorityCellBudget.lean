/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Descent/PriorityCellBudget.lean
  Original module: OAI.NumberTheory.DirichletL.Descent.PriorityCellBudget
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
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.SecondCellParameters
import RiemannHypothesis.Family003.NumberTheory.DirichletL.Descent.PriorityCellEnergy

namespace RiemannHypothesis.Family003

noncomputable section

namespace SevenEighths.InverseMoment
open InverseSecondSourceBlocks

theorem priority_cell_physical_budget
    (Z:ℝ) (hZ:1<Z) (d:BlockIndex)
    (M r ell V delta A B R j t eta tau pi eps epsmass b C:ℝ)
    (ray:ℂ) (hC:0≤C) (hb:1≤b)
    (hsource:scales d 0*scales d 2≤b*Z^(r-A-B-t))
    (hthreshold:b≤Z^(6*eta))
    (hmass:epsmass*(secondCount ell R j t (secondCellExponent Z d 0)
      (secondCellExponent Z d 1)+11*eta/2)≤pi) :
    let N:=secondCellColumnExponent Z (Z^(r-A-B-t)) d
    let Vchild:=secondFormalLabel B (secondCellExponent Z d 1) (secondCellExponent Z d 2) j+4*eta
    C*Z^(firstKappa M r ell V delta A B R)*Real.exp ((9/2:ℝ)*(eta*Real.log Z))*
      (Real.exp (6*(eta*Real.log Z))*
        ‖((Z^(firstPhysicalHeight M r ell V delta B j+12*eta+tau):ℝ):ℂ)*ray*
          ((scales d 1*scales d 2*Z^N:ℝ):ℂ)⁻¹‖)*
      Z^((secondCount ell R j t (secondCellExponent Z d 0) (secondCellExponent Z d 1)+11*eta/2)*(1+epsmass))*
      Z^(2*(max 0 N+Vchild)+eps)≤
    C*‖ray‖*Z^(r+3*ell+V+48*eta+tau+pi+eps) := by
  intro N Vchild
  have hz:0<Z:=zero_lt_one.trans hZ
  have hclip:=second_cell_clipping_width Z (Z^(r-A-B-t)) b eta d hZ
    (Real.rpow_pos_of_pos hz _) hb hsource hthreshold
  rw [second_cell_formal_column Z r A B t d hZ] at hclip
  have he:=physical_block_scalar_budget Z hZ.le M r ell V delta A B R j t
    (secondCellExponent Z d 0) (secondCellExponent Z d 1) (secondCellExponent Z d 2)
    eta tau pi (eps+8*eta) epsmass ray C hC hclip hmass
  dsimp only [N,Vchild]
  rw [second_cell_formal_column Z r A B t d hZ]
  rw [second_cell_scale_rpow Z d 1 hZ,second_cell_scale_rpow Z d 2 hZ] at he
  convert (preTransparency := .instances) he using 1 <;> congr 1 <;> ring_nf

end SevenEighths.InverseMoment

end

end RiemannHypothesis.Family003

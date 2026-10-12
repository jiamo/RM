/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/DirichletL/Detector/CentralBranchProduct.lean
  Original module: OAI.NumberTheory.DirichletL.Detector.CentralBranchProduct
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8 (preprints/The-Quasi-Riemann-Hypothesis-September-30-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: yes.
    - imports RiemannHypothesis.Family003.Compat.Backports (upstream-named lemmas ite_eq_left/ite_eq_right/dite_eq_left/dite_eq_right or Finset.*₀ product bounds, absent at the host pin)
-/
import RiemannHypothesis.Family003.NumberTheory.DirichletL.PrimeRows.CentralExpansion
import RiemannHypothesis.Family003.Compat.Backports

namespace RiemannHypothesis.Family003

noncomputable section
open scoped Classical BigOperators
namespace SevenEighths.ProbeCentralBranchProduct

theorem coupled_product_bound {ι : Type*} [Fintype ι]
    (L R : ℝ) (f g y : ι→ℝ) (hf : ∀i,0≤f i)
    (hsub : ∀J : Finset ι,L*(∏j ∈ J,g j)≤R*(∏j ∈ J,y j)) :
    L*(∏j : ι, (f j+g j))≤R*(∏j : ι, (f j+y j)) := by
  rw [Finset.prod_add,Finset.prod_add,Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_le_sum
  intro J hJ
  calc
    _ = (∏j ∈ J,f j)*(L*∏j ∈ Finset.univ\J,g j) := by ring
    _ ≤ (∏j ∈ J,f j)*(R*∏j ∈ Finset.univ\J,y j) :=
      mul_le_mul_of_nonneg_left (hsub _) (Finset.prod_nonneg (fun j _=>hf j))
    _ = _ := by ring

theorem three_branch_bound {N : ℕ} (L R E : ℝ)
    (A B T : Fin N→ℂ) (y p : Fin N→ℝ)
    (hL : 0≤L) (hR : 0≤R) (hE : 0≤E) (hy : ∀j,0≤y j) (hp : ∀j,1≤p j)
    (hA : ∀j,‖A j‖≤y j*p j) (hB : ∀j,‖B j‖≤y j*E)
    (hT : ∀J : Finset (Fin N),L*(∏j ∈ J,‖T j‖)≤R*(∏j ∈ J,y j)) :
    L*‖∏j : Fin N, (A j+B j+T j)‖≤R*(E+2)^N*(∏j : Fin N, y j)*(∏j : Fin N,p j) := by
  have hnorm : ‖∏j : Fin N, (A j+B j+T j)‖≤∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖) := by
    rw [norm_prod]
    apply Finset.prod_le_prod₀ (fun _ _=>norm_nonneg _)
    intro j _
    exact (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
  have hc := coupled_product_bound L R (fun j=>‖A j‖+‖B j‖) (fun j=>‖T j‖) y
    (fun j=>add_nonneg (norm_nonneg _) (norm_nonneg _)) hT
  have hpoint (j : Fin N) : (‖A j‖+‖B j‖)+y j≤y j*((E+2)*p j) := by
    have h := hp j
    have hp0 : 0≤p j := zero_le_one.trans h
    have he := mul_nonneg (show 0≤E+1 by linarith) (show 0≤p j-1 by linarith)
    have hm := mul_nonneg (hy j) he
    nlinarith [hA j,hB j]
  calc
    _ ≤ L*(∏j : Fin N,((‖A j‖+‖B j‖)+‖T j‖)) := mul_le_mul_of_nonneg_left hnorm hL
    _ ≤ R*(∏j : Fin N,((‖A j‖+‖B j‖)+y j)) := hc
    _ ≤ R*(∏j : Fin N, y j*((E+2)*p j)) := by
      apply mul_le_mul_of_nonneg_left _ hR
      exact Finset.prod_le_prod₀ (fun j _=>add_nonneg (add_nonneg (norm_nonneg _) (norm_nonneg _)) (hy j)) (fun j _=>hpoint j)
    _ = _ := by simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin];ring
end SevenEighths.ProbeCentralBranchProduct

end

end RiemannHypothesis.Family003

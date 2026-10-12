/-
Host-compatibility backport for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 (`Mathlib/Analysis/Normed/Operator/Extend.lean`,
Apache 2.0, Mathlib contributors) provides `LinearMap.extendOfIsometry`: a linear map `f : E → F`
into a Banach space with `‖f x‖ = ‖e x‖` for a linear map `e : E → Eₗ` of dense range extends to a
linear isometry `Eₗ → F`, together with `LinearMap.extendOfIsometry_eq`.  Neither exists at this
repository's Mathlib pin db584cd6.  The declarations below have the same names and argument
order as used by the absorbed proofs, and are built from the host's `LinearMap.extendOfNorm`.

Proof status: NEWLY PROVED FOR COMPATIBILITY.
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.Analysis.Normed.Operator.Extend

namespace LinearMap

variable {𝕜 E Eₗ F : Type*} [NontriviallyNormedField 𝕜] [AddCommGroup E] [Module 𝕜 E]
  [NormedAddCommGroup Eₗ] [NormedSpace 𝕜 Eₗ] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [CompleteSpace F]

theorem family003_extendOfNorm_norm (f : E →ₗ[𝕜] F) {e : E →ₗ[𝕜] Eₗ} (h_dense : DenseRange e)
    (h_norm : ∀ x, ‖f x‖ = ‖e x‖) (x : Eₗ) : ‖f.extendOfNorm e x‖ = ‖x‖ := by
  have hb : ∃ C, ∀ x, ‖f x‖ ≤ C * ‖e x‖ := ⟨1, fun x => by simp [h_norm]⟩
  refine h_dense.induction ?_ (isClosed_eq (by fun_prop) (by fun_prop)) x
  rintro _ ⟨y, rfl⟩
  rw [extendOfNorm_eq h_dense hb, h_norm]

/-- Extension of a norm-preserving linear map along a dense linear map to a linear isometry. -/
noncomputable def extendOfIsometry (f : E →ₗ[𝕜] F) {e : E →ₗ[𝕜] Eₗ} (h_dense : DenseRange e)
    (h_norm : ∀ x, ‖f x‖ = ‖e x‖) : Eₗ →ₗᵢ[𝕜] F where
  toLinearMap := (f.extendOfNorm e).toLinearMap
  norm_map' := family003_extendOfNorm_norm f h_dense h_norm

theorem extendOfIsometry_eq (f : E →ₗ[𝕜] F) {e : E →ₗ[𝕜] Eₗ} (h_dense : DenseRange e)
    (h_norm : ∀ x, ‖f x‖ = ‖e x‖) (x : E) : f.extendOfIsometry h_dense h_norm (e x) = f x :=
  extendOfNorm_eq h_dense ⟨1, fun x => by simp [h_norm]⟩ x

end LinearMap

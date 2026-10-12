/-
Host-compatibility backports for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

The absorbed proofs were written against Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612,
which has the `IntegrableOn` versions of the real/imaginary-part integrability lemmas
(`Mathlib/MeasureTheory/Integral/IntegrableOn.lean`, section `RCLike`; Mathlib is Apache 2.0,
copyright of the respective Mathlib authors).  At the host pin
(Mathlib db584cd6d46c92f209a44c0f1c829460d327499d) they are absent, so `hf.re` for
`hf : IntegrableOn f s μ` elaborates as `Integrable.re` and produces a goal of a different
shape.  The declarations below have exactly the upstream statements; the proofs are the
upstream one-line reductions to the `Integrable` lemmas, except `IntegrableOn.iff_ofReal`, whose
upstream proof uses `Integrable.iff_ofReal` (also absent at the host pin) and which is proved
here directly from `Integrable.ofReal` and `Integrable.re`.

Proof status: BACKPORTED (statements copied from upstream; one proof newly written).
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Function.L1Space.Integrable

namespace MeasureTheory

variable {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
variable {𝕜 : Type*} [RCLike 𝕜]

theorem IntegrableOn.iff_ofReal {f : α → ℝ} :
    IntegrableOn f s μ ↔ IntegrableOn (fun x ↦ (f x : 𝕜)) s μ :=
  ⟨fun hf => Integrable.ofReal hf, fun hf => by
    have h := Integrable.re hf
    simp only [RCLike.ofReal_re] at h
    exact h⟩

theorem IntegrableOn.ofReal {f : α → ℝ} (hf : IntegrableOn f s μ) :
    IntegrableOn (fun x ↦ (f x : 𝕜)) s μ :=
  Integrable.ofReal hf

theorem IntegrableOn.re_im_iff {f : α → 𝕜} :
    IntegrableOn (fun x ↦ RCLike.re (f x)) s μ ∧
      IntegrableOn (fun x ↦ RCLike.im (f x)) s μ ↔ IntegrableOn f s μ :=
  Integrable.re_im_iff

theorem IntegrableOn.re {f : α → 𝕜} (hf : IntegrableOn f s μ) :
    IntegrableOn (fun x ↦ RCLike.re (f x)) s μ :=
  Integrable.re hf

theorem IntegrableOn.im {f : α → 𝕜} (hf : IntegrableOn f s μ) :
    IntegrableOn (fun x ↦ RCLike.im (f x)) s μ :=
  Integrable.im hf

end MeasureTheory

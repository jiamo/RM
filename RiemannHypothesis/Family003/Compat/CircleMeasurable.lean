/-
Host-compatibility backport for the native absorption of openai/math, family 003.
  Origin: Mathlib file `Mathlib/MeasureTheory/Group/Circle.lean` at Mathlib revision
    d13f23b723b8a846827a245b89c10fc7d3f11612 (the upstream openai/math pin).  The file was
    added to Mathlib after this repository's Mathlib pin db584cd6d46c92f209a44c0f1c829460d327499d,
    and is imported by the third-party module PrimeNumberTheoremAnd.Wiener (via openai/math,
    source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).
  Original copyright: Copyright (c) 2026 Terence Tao. Released under Apache 2.0 license
    (Mathlib). Authors: Terence Tao.
  Proof status: ADAPTED (verbatim content of the Mathlib file, minus the module-system
    `module` / `public` keywords, which this repository does not use).
  Host compatibility edits: yes (this whole file is a compatibility backport).
-/
import Mathlib.Analysis.Complex.Circle
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex

/-!
# Measure-theoretic results about the circle

The Borel structure on `Circle` inherited from the ambient subtype, which makes
`Circle`-valued functions (such as the additive character `Real.fourierChar`) measurable.
-/

namespace Circle

instance : MeasurableSpace Circle := inferInstanceAs <| MeasurableSpace <| Subtype _

instance : BorelSpace Circle :=
  inferInstanceAs <| BorelSpace <| Subtype (· ∈ Metric.sphere (0 : ℂ) 1)

protected lemma measurable_coe : Measurable fun x : Circle ↦ (x : ℂ) := measurable_subtype_coe

protected lemma measurable_iff {X : Type*} [MeasurableSpace X] {f : X → Circle} :
    Measurable f ↔ Measurable fun x ↦ (f x : ℂ) := measurable_comap_iff

end Circle

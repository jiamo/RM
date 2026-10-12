/-
Host-compatibility backport for the native absorption of openai/math, family 003
(source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb).

Some absorbed statements quantify over an ideal `Q` with `[NeZero Q]` and use `O ⧸ Q` where a
`Finite (O ⧸ Q)` instance is needed, without declaring one.  At the upstream Mathlib pin
d13f23b723b8a846827a245b89c10fc7d3f11612 the instance is found by type-class search; at this
repository's Mathlib pin db584cd6 it is not, although the fact itself is
`Ring.HasFiniteQuotients.finiteQuotient`.  The instance below supplies it.

Proof status: NEWLY PROVED FOR COMPATIBILITY.
Host compatibility edits: yes (this whole file is a compatibility layer).
-/
import Mathlib.RingTheory.Ideal.Quotient.HasFiniteQuotients

/-- In a ring with finite quotients, the quotient by a non-zero ideal is finite. -/
instance Ideal.family003_finite_quotient_of_neZero {R : Type*} [CommRing R]
    [Ring.HasFiniteQuotients R] (I : Ideal R) [NeZero I] : Finite (R ⧸ I) :=
  Ring.HasFiniteQuotients.finiteQuotient (NeZero.ne I)

import Main
import RiemannHypothesis.Main

/-!
# Bridge: the alpo.ge theorem against this repository's statements

`Main` is the vendored alpo.ge tree (`vendor/alpo/lean/src/Main.lean`); `RiemannHypothesis.Main`
is this repository.  Both are compiled against the same pins (Lean v4.33.1, Mathlib
`0df444a3`), so they can be imported together.

The first three theorems below say: if the tree's `riemannHypothesis` checks, then it proves
this repository's statement of record `ZetaForm` (which is Mathlib's `RiemannHypothesis`,
by `abbrev`), and, through the equivalences proved here independently of the tree, the
strip form and the Dirichlet-eta form.  `EtaForm` is stated with `dirichletEta`, defined in
`RiemannHypothesis/Defs.lean` by its paired series, without analytic continuation; so the
last theorem ties the tree's claim to an elementary statement whose meaning does not depend on
how Mathlib defines `riemannZeta` outside `re s > 1`.

These are *not* theorems of this repository: they live in `vendor/alpo`, are compiled only by
`vendor/alpo/tools/bridge.sh` after the tree has been built, and depend on the tree being
correct.  The `#print axioms` lines below must show only `propext`, `Classical.choice`,
`Quot.sound`.
-/

theorem alpo_zetaForm : RiemannHypothesis.ZetaForm :=
  riemannHypothesis

theorem alpo_zetaStripForm : RiemannHypothesis.ZetaStripForm :=
  RiemannHypothesis.zeta_iff_zeta_strip.mp riemannHypothesis

theorem alpo_etaForm : RiemannHypothesis.EtaForm :=
  RiemannHypothesis.zeta_iff_eta.mp riemannHypothesis

/-! ## Cross-checks inside the tree

The tree states RH twice: as Mathlib's `RiemannHypothesis` and as its own
`RiemannZetaZerosOnLine` (`Statements.lean`).  The two are the same proposition. -/

theorem alpo_statements_agree : RiemannZetaZerosOnLine ↔ RiemannHypothesis.ZetaForm :=
  Iff.rfl

/-! A second, independent route to RH: the tree's GRH theorem `LFunction_eq_zero_re`, applied
to the Dirichlet character mod 1, whose `L`-function is `riemannZeta`
(`DirichletCharacter.LFunction_modOne_eq`, Mathlib).  It does not use `riemannHypothesis`;
two separately stated claims of the tree must land on the same statement of this repository. -/

theorem alpo_zetaStripForm_of_grh : RiemannHypothesis.ZetaStripForm :=
  fun s h0 h1 hz => LFunction_eq_zero_re 1 1 s h0 h1
    (by rw [DirichletCharacter.LFunction_modOne_eq]; exact hz)

theorem alpo_etaForm_of_grh : RiemannHypothesis.EtaForm :=
  RiemannHypothesis.zeta_strip_iff_eta.mp alpo_zetaStripForm_of_grh

#print axioms alpo_zetaForm
#print axioms alpo_zetaStripForm
#print axioms alpo_etaForm
#print axioms alpo_statements_agree
#print axioms alpo_zetaStripForm_of_grh
#print axioms alpo_etaForm_of_grh

/-
Native absorption of openai/math, family 003 ("The quasi-Riemann hypothesis").
  Source repository: github.com/openai/math
  Original path: lean/OAI/NumberTheory/SiegelZeros/Structure/ThetaJetBridge.lean
  Original module: OAI.NumberTheory.SiegelZeros.Structure.ThetaJetBridge
  Source revision: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
  Paper: Uniform exclusion of Landau-Siegel zeros (preprints/Uniform-exclusion-of-Landau-Siegel-zeros-October-1-2026)
  Upstream licence: Apache License 2.0 (see LICENSES/openai-math-LICENSE and NOTICE).
  The upstream file carries no per-file copyright or author line; openai/math states that
  its manuscripts and proof artifacts were produced by an internal OpenAI model.
  Proof status: ADAPTED (upstream Lean proof; module prefix OAI -> RiemannHypothesis.Family003,
  namespace OAI -> RiemannHypothesis.Family003).
  Host compatibility edits: none.
-/
import RiemannHypothesis.Family003.NumberTheory.SiegelZeros.Determinants.ThetaDivisibility

namespace RiemannHypothesis.Family003

namespace SiegelZeros


namespace SiegelZerosAwei.W60

variable {R : Type*} [CommRing R]

theorem theta_eq_eigenvalue (u v : R) (n : Fin 4 →₀ ℕ) :
    Awei.W39.theta u v (fun i => (n i : ℤ)) =
      WeightedTorusJets.W18.eigenvalue ![1, u, v, u * v] n := by
  simp [Awei.W39.theta, WeightedTorusJets.W18.eigenvalue, Fin.sum_univ_succ]
  ring

def thetaDirections (u v : R) : Fin 3 → Fin 4 → R :=
  ![![1, u, v, u * v], ![1, -u, v, -u * v], ![1, -u, -v, (-u) * (-v)]]

theorem theta_row_eq_actual_jet (u v : R) (n : Fin 4 →₀ ℕ) (a : Fin 3 → ℕ) :
    WeightedTorusJets.W40.rowEntry
      (Awei.W39.theta u v (fun i => (n i : ℤ)))
      (Awei.W39.theta (-u) v (fun i => (n i : ℤ)))
      (Awei.W39.theta (-u) (-v) (fun i => (n i : ℤ))) (a 0) (a 1) (a 2) =
      MvPolynomial.eval (fun _ => (1 : R))
        (WeightedTorusJets.W19.mixedInvariant (thetaDirections u v) a
          (MvPolynomial.monomial n 1)) := by
  rw [WeightedTorusJets.W19.derivative_row_at_one]
  simp only [thetaDirections, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons, theta_eq_eigenvalue,
    WeightedTorusJets.W40.rowEntry]

theorem map_theta (f : R →+* R) (u v : R) (n : Fin 4 → ℤ) :
    f (Awei.W39.theta u v n) = Awei.W39.theta (f u) (f v) n := by
  simp [Awei.W39.theta]

open scoped BigOperators

theorem actual_jet_determinant_dvd
    {ι K : Type*} [Fintype ι] [DecidableEq ι] [LinearOrder ι] [CommRing K]
    (f : R →+* K) (hf : Function.Injective f)
    (H p : ℕ) [Fact p.Prime] (hpH : H < p) (hp2 : p ≠ 2)
    (u v : R) (d : ℤ) (hu : u ^ 2 = (d : R)) (hv : v ^ 2 = 2)
    (hd : legendreSym p d = -1) (n : ι → Fin 4 →₀ ℕ) (a : ι → Fin 3 → ℕ)
    (hearlier : EarlierSpan f H
      (fun j => Awei.W39.theta u v (fun i => (n j i : ℤ)))
      (fun j => Awei.W39.theta (-u) v (fun i => (n j i : ℤ)))
      (fun j => Awei.W39.theta (-u) (-v) (fun i => (n j i : ℤ)))
      (fun i => a i 0) (fun i => a i 1) (fun i => a i 2)) :
    (p : R) ^ (∑ i, a i 0 / p) ∣
      Matrix.det (fun i j => MvPolynomial.eval (fun _ => (1 : R))
        (WeightedTorusJets.W19.mixedInvariant (thetaDirections u v) (a i)
          (MvPolynomial.monomial (n j) 1)) : Matrix ι ι R) := by
  have hmatrix :
      (fun i j => MvPolynomial.eval (fun _ => (1 : R))
        (WeightedTorusJets.W19.mixedInvariant (thetaDirections u v) (a i)
          (MvPolynomial.monomial (n j) 1)) : Matrix ι ι R) =
      rows (fun j => Awei.W39.theta u v (fun i => (n j i : ℤ)))
        (fun j => Awei.W39.theta (-u) v (fun i => (n j i : ℤ)))
        (fun j => Awei.W39.theta (-u) (-v) (fun i => (n j i : ℤ)))
        (fun i => a i 0) (fun i => a i 1) (fun i => a i 2) := by
    ext i j
    exact (theta_row_eq_actual_jet u v (n j) (a i)).symm
  rw [hmatrix]
  exact theta_determinant_dvd f hf H p hpH hp2 u v d hu hv hd
    (fun j i => (n j i : ℤ)) (fun i => a i 0) (fun i => a i 1)
    (fun i => a i 2) hearlier

end SiegelZerosAwei.W60


end SiegelZeros

end RiemannHypothesis.Family003

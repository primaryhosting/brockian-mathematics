import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Matrix Polynomial Finset

/-- A primitive 20-th root of unity. -/

theorem huckel_C20_charpoly :
    ((SimpleGraph.cycleGraph 20).adjMatrix ℂ).charpoly =
      ∏ k ∈ Finset.range 20,
        (Polynomial.X - Polynomial.C ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ)) := by
  have hQP : Qm * Pm = 1 := mul_eq_one_comm.mp Pm_mul_Qm
  let U : (Matrix (Fin 20) (Fin 20) ℂ)ˣ := ⟨Pm, Qm, Pm_mul_Qm, hQP⟩
  have hA : (SimpleGraph.cycleGraph 20).adjMatrix ℂ
      = (U : Matrix (Fin 20) (Fin 20) ℂ) * Dm * ((U⁻¹ : (Matrix (Fin 20) (Fin 20) ℂ)ˣ) :
        Matrix (Fin 20) (Fin 20) ℂ) := by
    show _ = Pm * Dm * Qm
    rw [← adj_mul_Pm, mul_assoc, Pm_mul_Qm, mul_one]
  rw [hA, Matrix.charpoly_units_conj, Dm, Matrix.charpoly_diagonal,
    ← Fin.prod_univ_eq_prod_range
      (fun k => Polynomial.X - Polynomial.C ((2 * Real.cos (2 * Real.pi * k / 20) : ℝ) : ℂ)) 20]
  exact Finset.prod_congr rfl (fun k _ => by rw [ee_add_inv])

/-- **Hückel theory for C₂₀.** The eigenvalues of the adjacency matrix of the cycle graph
`C₂₀` are exactly the numbers `2 cos (2πk/20)` for `k = 0, …, 19`. -/

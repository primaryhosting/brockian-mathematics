import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Matrix

/-- `ec n m = exp (2 π i m / n)`, an `n`-th root of unity raised to the power `m`. -/

theorem huckel_cycle_eigenvector (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    (SimpleGraph.cycleGraph n).adjMatrix ℂ *ᵥ (fun j : Fin n => ec n ((k.val : ℤ) * j.val))
      = ((2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ) •
        (fun j : Fin n => ec n ((k.val : ℤ) * j.val)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  funext i
  have h := adjMatrix_mul_dft (m := m) (by omega) i k
  rw [Matrix.mul_apply] at h
  simp only [dftMatrix] at h
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ j : Fin (m + 2), (SimpleGraph.cycleGraph (m + 2)).adjMatrix ℂ i j *
      ec (m + 2) ((k.val : ℤ) * j.val))
      = ∑ j : Fin (m + 2), (SimpleGraph.cycleGraph (m + 2)).adjMatrix ℂ i j *
        ec (m + 2) ((j.val : ℤ) * k.val) from
    Finset.sum_congr rfl (fun j _ => by rw [mul_comm (j.val : ℤ)]), h]
  rw [huckelEnergy, mul_comm (k.val : ℤ)]

end Chem


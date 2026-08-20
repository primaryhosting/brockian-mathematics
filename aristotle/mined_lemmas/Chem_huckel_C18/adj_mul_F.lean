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

open Complex Polynomial Matrix

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma adj_mul_F : ((SimpleGraph.cycleGraph 18).adjMatrix ℂ) * F = F * D := by
  ext i k
  have hL : (((SimpleGraph.cycleGraph 18).adjMatrix ℂ) * F) i k = F (i - 1) k + F (i + 1) k := by
    show (((SimpleGraph.cycleGraph 18).adjMatrix ℂ) *ᵥ (fun j => F j k)) i = _
    rw [SimpleGraph.adjMatrix_mulVec_apply, SimpleGraph.cycleGraph_neighborFinset (n := 16),
      Finset.sum_pair (fin18_sub_one_ne_add_one i)]
  rw [hL, D, Matrix.mul_diagonal]
  simp only [F, Matrix.of_apply, fin18_sub_one]
  have e1 : ee (((i + 17 : Fin 18) : ℕ) * (k : ℕ)) = ee (((((i : ℕ) + 17 : ℕ)) : ℤ) * (k : ℕ)) := by
    apply ee_mul_congr; simp [Fin.val_add]
  have e2 : ee (((i + 1 : Fin 18) : ℕ) * (k : ℕ)) = ee (((((i : ℕ) + 1 : ℕ)) : ℤ) * (k : ℕ)) := by
    apply ee_mul_congr; simp [Fin.val_add]
  rw [e1, e2]
  simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  have E1 : ee (((((i : ℕ) : ℤ)) + 17) * ((k : ℕ) : ℤ))
      = ee (((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)) * ee (-((k : ℕ) : ℤ)) := by
    rw [show (((((i : ℕ) : ℤ)) + 17) * ((k : ℕ) : ℤ))
          = ((i : ℕ) : ℤ) * ((k : ℕ) : ℤ) + 17 * ((k : ℕ) : ℤ) by ring, ee_add]
    congr 1
    exact ee_congr ⟨(k : ℕ), by ring⟩
  have E2 : ee (((((i : ℕ) : ℤ)) + 1) * ((k : ℕ) : ℤ))
      = ee (((i : ℕ) : ℤ) * ((k : ℕ) : ℤ)) * ee (((k : ℕ) : ℤ)) := by
    rw [show (((((i : ℕ) : ℤ)) + 1) * ((k : ℕ) : ℤ))
          = ((i : ℕ) : ℤ) * ((k : ℕ) : ℤ) + ((k : ℕ) : ℤ) by ring, ee_add]
  rw [E1, E2, ← mul_add, add_comm (ee (-((k : ℕ) : ℤ))) (ee ((k : ℕ) : ℤ)), ee_cos]
  push_cast
  ring

/-- **Hückel theory for the C₁₈ annulene ring.**  The characteristic polynomial of the
adjacency matrix of the cycle graph `C₁₈` factors as `∏ k, (X - 2 cos (2πk/18))`, i.e. the
adjacency eigenvalues of `C₁₈` are exactly `2 cos (2πk/18)` for `k = 0, …, 17`. -/

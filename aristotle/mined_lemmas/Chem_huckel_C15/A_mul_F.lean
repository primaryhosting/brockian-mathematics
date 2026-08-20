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

/-!
# Hückel spectrum of the cycle `C₁₅`

The adjacency matrix of the cycle graph `C₁₅` has characteristic polynomial
`∏_{k=0}^{14} (X - 2cos(2πk/15))`; equivalently its eigenvalues are the numbers
`2cos(2πk/15)` for `k = 0, …, 14`.
-/

namespace Chem

open Matrix Polynomial Complex

/-- A primitive 15-th root of unity. -/

theorem A_mul_F : A * F = F * D := by
  ext i k
  rw [A, SimpleGraph.adjMatrix_mul_apply, SimpleGraph.cycleGraph_neighborFinset]
  have hne : (i - 1 : Fin 15) ≠ i + 1 := by
    intro h
    have h1 : (i - 1 : Fin 15) + 1 = (i + 1) + 1 := by rw [h]
    rw [sub_add_cancel, add_assoc] at h1
    simp at h1
  rw [Finset.sum_pair hne]
  -- compute the two neighbouring entries
  have key : ∀ a : Fin 15, (a + 1 : Fin 15).val = (a.val + 1) % 15 := by
    intro a; rw [Fin.val_add]; rfl
  have hplus : w ^ ((i + 1 : Fin 15)).val = w ^ i.val * w := by
    rw [← pow_succ]
    apply w_pow_congr
    rw [key i]
    omega
  have hminus : w ^ ((i - 1 : Fin 15)).val * w = w ^ i.val := by
    rw [← pow_succ]
    apply w_pow_congr
    rw [← key (i - 1), sub_add_cancel]
    omega
  have hminus' : w ^ ((i - 1 : Fin 15)).val = w ^ i.val * w⁻¹ := by
    field_simp [w_ne_zero] at hminus ⊢
    linear_combination hminus
  simp only [D, Matrix.mul_diagonal, F_apply]
  rw [hplus, hminus', mul_pow, mul_pow, ← w_pow_add_inv k.val, inv_pow]
  ring


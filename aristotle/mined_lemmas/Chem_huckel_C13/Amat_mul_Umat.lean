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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
# Hückel theory for the 13-cycle

The adjacency matrix of the cycle graph `C₁₃` has spectrum `{2 cos (2πk/13) | k = 0, …, 12}`.

The proof diagonalizes the adjacency matrix by the discrete Fourier matrix
`U i j = ω^(i * j)`, where `ω = exp (2πi/13)` is a primitive 13-th root of unity.
-/

namespace Chem

open Complex Matrix

/-- A primitive 13-th root of unity. -/

lemma Amat_mul_Umat : Amat * Umat = Umat * Matrix.diagonal hueckelEigen := by
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ l : Fin 13, Amat i l * Umat l j
      = (if l = i - 1 then Umat l j else 0) + (if l = i + 1 then Umat l j else 0) := by
    intro l
    rw [Amat_apply]
    have hne : (i - 1 : Fin 13) ≠ i + 1 := sub_one_ne_add_one i
    by_cases h1 : l = i - 1
    · have h2 : l ≠ i + 1 := by rw [h1]; exact hne
      simp [h1, hne]
    · by_cases h2 : l = i + 1 <;> simp [h1, h2, Ne.symm hne]
  rw [Finset.sum_congr rfl (fun l _ => key l), Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [Matrix.mul_diagonal]
  simp only [Umat, hueckelEigen]
  rw [sub_one_mul, add_one_mul', zeta_add, zeta_add, ← zeta_neg_add_self j]
  ring

/-- **Hückel theory for the 13-membered carbon ring.**  The eigenvalues (spectrum) of the
adjacency matrix of the cycle graph `C₁₃` are exactly the numbers `2 cos (2πk/13)`
for `k = 0, 1, …, 12`. -/

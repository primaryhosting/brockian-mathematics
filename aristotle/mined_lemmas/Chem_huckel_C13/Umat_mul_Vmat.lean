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

lemma Umat_mul_Vmat : Umat * Vmat = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have key : ∀ l : Fin 13, Umat i l * Vmat l j = (13 : ℂ)⁻¹ * zeta (l * (i - j)) := by
    intro l
    simp only [Umat, Vmat]
    rw [← mul_sub_distrib i j l, zeta_add]
    ring
  rw [Finset.sum_congr rfl (fun l _ => key l), ← Finset.mul_sum, sum_zeta]
  by_cases h : i = j
  · subst h
    simp [Matrix.one_apply_eq]
  · rw [if_neg (sub_ne_zero.mpr h)]
    simp [Matrix.one_apply_ne h]


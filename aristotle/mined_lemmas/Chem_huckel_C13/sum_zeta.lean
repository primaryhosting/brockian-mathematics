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

lemma sum_zeta (c : Fin 13) :
    (∑ l : Fin 13, zeta (l * c)) = if c = 0 then 13 else 0 := by
  by_cases hc : c = 0
  · subst hc; simp [zeta]
  · simp only [hc, if_false]
    rw [Finset.sum_congr rfl (fun l _ => zeta_pow l c)]
    rw [Fin.sum_univ_eq_sum_range (fun m => (zeta c) ^ m) 13]
    rw [geom_sum_eq (zeta_ne_one hc), zeta_pow13]
    simp


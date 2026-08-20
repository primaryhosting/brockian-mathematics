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
# Hückel spectrum of the cycle graph `C₁₁`

We compute the adjacency spectrum of the cycle graph `C₁₁` (the carbon skeleton used in
simple Hückel theory for an 11-membered annulene ring): the eigenvalues of the adjacency
matrix of `SimpleGraph.cycleGraph 11` are exactly `2 * cos (2 * π * k / 11)` for `k = 0, …, 10`.

The proof diagonalises the adjacency matrix by the discrete Fourier (Vandermonde) matrix
built from the primitive 11-th root of unity `ω = exp (2πi/11)`.
-/

namespace Chem

open Polynomial Complex Matrix

/-- The primitive 11-th root of unity `exp (2πi/11)`. -/

lemma om_pred (j : Fin 11) : om ^ ((j - 1 : Fin 11) : ℕ) = om ^ (j : ℕ) * om⁻¹ := by
  have h := om_fin_add (j - 1) 1
  rw [sub_add_cancel] at h
  have h1 : ((1 : Fin 11) : ℕ) = 1 := rfl
  rw [h1, pow_one] at h
  field_simp [om_ne_zero] at h ⊢
  linear_combination -h

/-- Each Hückel eigenvalue is `ω ^ k + ω ^ (-k)`. -/

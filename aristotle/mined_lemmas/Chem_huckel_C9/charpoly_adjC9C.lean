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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Chem

open Polynomial Matrix

/-! ## The adjacency matrix of the cycle graph `C₉` -/

/-- The adjacency matrix of the cycle graph `C₉`, i.e. the Hückel matrix of the
cyclononatetraenyl π-system with `α = 0` and `β = 1`. -/

lemma charpoly_adjC9C : adjC9C.charpoly = diagC9.charpoly := by
  have hdet : IsUnit (fourier9.det) := isUnit_iff_ne_zero.mpr fourier9_det_ne_zero
  have h1 : fourier9⁻¹ * (adjC9C * fourier9) = diagC9 := by
    rw [adjC9C_mul_fourier9, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hdet, Matrix.one_mul]
  calc adjC9C.charpoly
      = (adjC9C * (fourier9 * fourier9⁻¹)).charpoly := by
        rw [Matrix.mul_nonsing_inv _ hdet, Matrix.mul_one]
    _ = ((adjC9C * fourier9) * fourier9⁻¹).charpoly := by rw [Matrix.mul_assoc]
    _ = (fourier9⁻¹ * (adjC9C * fourier9)).charpoly := Matrix.charpoly_mul_comm _ _
    _ = diagC9.charpoly := by rw [h1]

/-! ## The main theorem -/

/-- **Hückel theory for C₉.** The characteristic polynomial of the adjacency matrix of the
cycle graph `C₉` is `∏ k, (X - 2 cos (2πk/9))`; equivalently, the adjacency eigenvalues of
`C₉`, listed with multiplicity, are `2 cos (2πk/9)` for `k = 0, …, 8`. -/

import Mathlib

/-!
# Atiyah Singer Index
Category: Frontier — Fields Medal Work
Target: Frontier.atiyah_singer_index
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

open Module Polynomial

/-! ## The analytic index

The *analytic index* of an operator `D` is `dim ker D - dim coker D`.  This is the
standard Fredholm index, written here for a `ℂ`-linear map between arbitrary
`ℂ`-vector spaces; it is the meaningful invariant exactly when both the kernel and
the cokernel are finite dimensional (`Module.finrank` returns `0` on infinite
dimensional spaces). -/

/-- The analytic (Fredholm) index `dim ker D - dim coker D` of a linear operator `D`. -/

theorem finrank_coker_toeplitzPow (n : ℕ) :
    finrank ℂ (Polynomial ℂ ⧸ LinearMap.range (toeplitzPow n)) = n := by
  have e1 : (Polynomial ℂ ⧸ LinearMap.range (toeplitzPow n)) ≃ₗ[ℂ]
      (Polynomial ℂ ⧸ LinearMap.ker (Polynomial.modByMonicHom (X ^ n : ℂ[X]))) :=
    Submodule.quotEquivOfEq _ _ (range_toeplitzPow n)
  have e2 := (Polynomial.modByMonicHom (X ^ n : ℂ[X])).quotKerEquivRange
  have e3 : (LinearMap.range (Polynomial.modByMonicHom (X ^ n : ℂ[X])) :
      Submodule ℂ (Polynomial ℂ)) ≃ₗ[ℂ] (Polynomial.degreeLT ℂ n) :=
    LinearEquiv.ofEq _ _ (range_modByMonicHom_X_pow n)
  rw [(e1.trans (e2.trans (e3.trans (Polynomial.degreeLTEquiv ℂ n)))).finrank_eq]
  simp

/-- The analytic index of the Toeplitz operator with symbol `z ↦ z ^ n` is `-n`. -/

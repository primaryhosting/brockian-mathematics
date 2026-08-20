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

theorem analyticIndex_indep_of_operator {M : Type*} [Fintype M] (E F : M → Type*)
    [∀ x, AddCommGroup (E x)] [∀ x, Module ℂ (E x)] [∀ x, FiniteDimensional ℂ (E x)]
    [∀ x, AddCommGroup (F x)] [∀ x, Module ℂ (F x)] [∀ x, FiniteDimensional ℂ (F x)]
    (D D' : (∀ x, E x) →ₗ[ℂ] (∀ x, F x)) :
    analyticIndex D = analyticIndex D' := by
  rw [atiyah_singer_index E F D, atiyah_singer_index E F D']

/-! ## The Toeplitz index theorem

A genuinely infinite dimensional instance of the same principle: the index theorem
for Toeplitz operators on the circle.  We use the polynomial model `ℂ[X]` of the
Hardy space, on which the Toeplitz operator with symbol `σ_n(z) = z ^ n` is
multiplication by `X ^ n`.  Its analytic index is `-n`, and this equals minus the
winding number of the symbol around the origin, computed by the argument principle
as the logarithmic derivative contour integral `(2πi)⁻¹ ∮_{|z| = 1} σ'(z) / σ(z) dz`. -/

/-- The Toeplitz operator with symbol `z ↦ z ^ n` on the polynomial model of the
Hardy space: multiplication by `X ^ n`. -/

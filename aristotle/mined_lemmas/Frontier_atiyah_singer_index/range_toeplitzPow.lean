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

theorem range_toeplitzPow (n : ℕ) :
    LinearMap.range (toeplitzPow n) = LinearMap.ker (Polynomial.modByMonicHom (X ^ n : ℂ[X])) := by
  ext p
  simp only [LinearMap.mem_range, LinearMap.mem_ker, Polynomial.modByMonicHom_apply,
    Polynomial.modByMonic_eq_zero_iff_dvd (Polynomial.monic_X_pow (R := ℂ) n)]
  constructor
  · rintro ⟨q, rfl⟩; exact ⟨q, rfl⟩
  · rintro ⟨q, rfl⟩; exact ⟨q, rfl⟩

/-- Reduction modulo `X ^ n` surjects `ℂ[X]` onto the polynomials of degree `< n`. -/

/-
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Fta Algebra
Category: Pure Mathematics
Target: Math.fta_algebra
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

open Polynomial

/-- **Fundamental theorem of algebra**: every nonconstant complex polynomial has a root.
Here "nonconstant" is expressed as `∀ c, p ≠ C c`.
The key Mathlib ingredient is `Complex.exists_root`. -/
theorem fta_algebra {p : ℂ[X]} (hp : ∀ c : ℂ, p ≠ C c) : ∃ z : ℂ, p.eval z = 0 := by
  have hdeg : 0 < p.degree := by
    rcases lt_or_ge 0 p.degree with h | h
    · exact h
    · exact absurd (Polynomial.eq_C_of_degree_le_zero h) (hp _)
  obtain ⟨z, hz⟩ := Complex.exists_root hdeg
  exact ⟨z, hz⟩

/-- Variant phrasing of the fundamental theorem of algebra, with the hypothesis
that the degree is positive. -/
theorem fta_algebra_degree {p : ℂ[X]} (hp : 0 < p.degree) : ∃ z : ℂ, p.eval z = 0 :=
  Complex.exists_root hp

end Math

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


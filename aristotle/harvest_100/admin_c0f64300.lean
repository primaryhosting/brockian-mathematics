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
Here "nonconstant" is expressed as `0 < f.degree`.
This follows from Mathlib's `Complex.exists_root`. -/
theorem fta_algebra {f : ℂ[X]} (hf : 0 < f.degree) : ∃ z : ℂ, f.IsRoot z :=
  Complex.exists_root hf

/-- Variant phrasing: a complex polynomial that is not a constant polynomial has a root. -/
theorem fta_algebra' {f : ℂ[X]} (hf : ¬ ∃ c : ℂ, f = C c) : ∃ z : ℂ, f.IsRoot z := by
  exact fta_algebra (not_le.mp fun h => hf ⟨f.coeff 0, eq_C_of_degree_le_zero h⟩)

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


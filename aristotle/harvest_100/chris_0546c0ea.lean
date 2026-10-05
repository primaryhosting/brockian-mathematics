/-
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib.SetTheory.Ordinal.Veblen

/-!
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

/-- `ε₀` is a fixed point of ordinal `ω`-exponentiation: `ω ^ ε₀ = ε₀`. -/
theorem epsilon0_fixed_point : (ω : Ordinal) ^ ε₀ = ε₀ :=
  omega0_opow_epsilon 0

/-- `ε₀` is the *least* fixed point of ordinal `ω`-exponentiation:
any ordinal `o` with `ω ^ o = o` satisfies `ε₀ ≤ o`. -/
theorem epsilon0_least_fixed_point {o : Ordinal} (h : (ω : Ordinal) ^ o = o) : ε₀ ≤ o :=
  epsilon_zero_le_of_omega0_opow_le h.le

end Ordinal

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


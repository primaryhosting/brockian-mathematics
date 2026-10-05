/-
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 rejects a module docstring `/-! ... -/` before `import`; the same header
-- is repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
Verification: verified (axiom-clean: propext, Classical.choice, Quot.sound)
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

open scoped Ordinal

/-- `ε₀` is a fixed point of ordinal `ω`-exponentiation: `ω ^ ε₀ = ε₀`. -/
theorem epsilon0_fixed_point : ω ^ ε₀ = ε₀ :=
  omega0_opow_epsilon 0

/-- `ε₀` is the *least* ordinal that is a fixed point of `ω`-exponentiation. -/
theorem epsilon0_least_fixed_point (o : Ordinal) (h : ω ^ o = o) : ε₀ ≤ o :=
  epsilon_zero_le_of_omega0_opow_le h.le

/-- `ε₀` is the least fixed point of `ω`-exponentiation. -/
theorem epsilon0_isLeast_fixed_point :
    IsLeast {o : Ordinal | ω ^ o = o} ε₀ :=
  ⟨epsilon0_fixed_point, fun _ h => epsilon0_least_fixed_point _ h⟩

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


/-
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` commands to precede every other command, including
-- module doc comments (`/-! ... -/`), so the required header is reproduced above as a
-- plain block comment and again below as the module docstring.

import Mathlib

/-!
# Epsilon 0 Fixed Point
Category: Frontier Wave 2 (deeper machinery)
Target: Ordinal.epsilon0_fixed_point
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Ordinal

open scoped Ordinal

/-- `ε₀` is a fixed point of ordinal `ω`-exponentiation: `ω ^ ε₀ = ε₀`.
This is the `o = 0` case of Mathlib's `Ordinal.omega0_opow_epsilon`. -/

theorem epsilon0_isLeast_fixed_point :
    IsLeast {o : Ordinal | ω ^ o = o} ε₀ :=
  ⟨epsilon0_fixed_point, fun _ h ↦ epsilon0_least_fixed_point h⟩

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


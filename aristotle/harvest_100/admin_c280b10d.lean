import Mathlib

/-!
# Aleph 0 Add Aleph 0
Category: Frontier — Set Theory
Target: Infinity.aleph0_add_aleph0
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

namespace Infinity

/-- Cardinal arithmetic: `ℵ₀ + ℵ₀ = ℵ₀`. -/
theorem aleph0_add_aleph0 : Cardinal.aleph0 + Cardinal.aleph0 = Cardinal.aleph0 :=
  Cardinal.add_eq_self le_rfl

/-- Cardinal arithmetic: `ℵ₀ * ℵ₀ = ℵ₀`. -/
theorem aleph0_mul_aleph0 : Cardinal.aleph0 * Cardinal.aleph0 = Cardinal.aleph0 :=
  Cardinal.mul_eq_self le_rfl

end Infinity


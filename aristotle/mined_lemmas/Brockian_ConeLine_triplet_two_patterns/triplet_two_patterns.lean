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

/-
# Triplet Two Patterns
Category: Cone Line
Target: Brockian.ConeLine.triplet_two_patterns
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Triplet Two Patterns
Category: Cone Line
Target: Brockian.ConeLine.triplet_two_patterns
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`, i.e. `q % 5 ≠ 0`. -/

theorem triplet_two_patterns {p : ℕ} (hp : Nat.Prime p) (hp2 : Nat.Prime (p + 2))
    (hp6 : Nat.Prime (p + 6)) (h5 : 5 < p) :
    (p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2) ∨
      (p % 5 = 2 ∧ (p + 2) % 5 = 4 ∧ (p + 6) % 5 = 3) := by
  have h0 : p % 5 ≠ 0 := mod_five_ne_zero_of_prime hp h5
  have h2 : (p + 2) % 5 ≠ 0 := mod_five_ne_zero_of_prime hp2 (by omega)
  have h6 : (p + 6) % 5 ≠ 0 := mod_five_ne_zero_of_prime hp6 (by omega)
  omega

end Brockian.ConeLine


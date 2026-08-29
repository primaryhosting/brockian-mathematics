/-
# Square Ray Primes Mod 20
Category: Cone Line
Target: Brockian.ConeLine.square_ray_primes_mod20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Brockian.ConeLine

/-- A prime `p > 5` with `p ≡ 1` or `4 (mod 5)` satisfies `p % 20 ∈ {1, 9, 11, 19}`. -/
theorem square_ray_primes_mod20 (p : ℕ) (hp : Nat.Prime p) (h5 : 5 < p)
    (h : p % 5 = 1 ∨ p % 5 = 4) :
    p % 20 = 1 ∨ p % 20 = 9 ∨ p % 20 = 11 ∨ p % 20 = 19 := by
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  omega

end Brockian.ConeLine


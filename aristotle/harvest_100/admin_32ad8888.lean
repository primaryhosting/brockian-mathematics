import Mathlib

/-!
# Sexy Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.sexy_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- A sexy prime pair `(p, p + 6)` with `p > 5` travels exactly the roads
`1 → 2`, `2 → 3`, `3 → 4` modulo `5`. -/
theorem sexy_prime_roads (p : ℕ) (hp : Nat.Prime p) (hq : Nat.Prime (p + 6))
    (h5 : 5 < p) :
    (p % 5, (p + 6) % 5) = (1, 2) ∨ (p % 5, (p + 6) % 5) = (2, 3) ∨
      (p % 5, (p + 6) % 5) = (3, 4) := by
  have hp5 : p % 5 ≠ 0 := by
    intro h
    rcases (hp.eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero h)) with h' | h' <;> omega
  have hq5 : (p + 6) % 5 ≠ 0 := by
    intro h
    rcases (hq.eq_one_or_self_of_dvd 5 (Nat.dvd_of_mod_eq_zero h)) with h' | h' <;> omega
  have := Nat.mod_lt p (show 0 < 5 by norm_num)
  have h6 : (p + 6) % 5 = (p % 5 + 1) % 5 := by omega
  simp only [Prod.mk.injEq]
  omega

end Brockian.ConeLine

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


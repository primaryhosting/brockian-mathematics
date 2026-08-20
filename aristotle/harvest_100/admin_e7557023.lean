import Mathlib

/-!
# Sophie Germain Avoids Ray 2
Category: Cone Line
Target: Brockian.ConeLine.sophie_germain_avoids_ray2
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ConeLine

/-- A Sophie Germain prime `p > 5` (both `p` and `2p+1` prime) never sits on ray 2:
`p ≡ 2 (mod 5)` would force `5 ∣ 2p+1`. The remaining "roads" are
`1 → 3`, `3 → 2` and `4 → 4`. -/
theorem sophie_germain_avoids_ray2 (p : ℕ) (hp : Nat.Prime p)
    (hq : Nat.Prime (2 * p + 1)) (h5 : 5 < p) :
    p % 5 ≠ 2 ∧
      ((p % 5, (2 * p + 1) % 5) = (1, 3) ∨
        (p % 5, (2 * p + 1) % 5) = (3, 2) ∨
        (p % 5, (2 * p + 1) % 5) = (4, 4)) := by
  -- `5 ∤ p` and `5 ∤ 2p+1`, since both are primes exceeding `5`.
  have hpd : ¬ (5 ∣ p) := by
    intro h
    rcases hp.eq_one_or_self_of_dvd 5 h with h' | h' <;> omega
  have hqd : ¬ (5 ∣ 2 * p + 1) := by
    intro h
    rcases hq.eq_one_or_self_of_dvd 5 h with h' | h' <;> omega
  have key : (2 * p + 1) % 5 = (2 * (p % 5) + 1) % 5 := by
    simp [Nat.add_mod, Nat.mul_mod]
  have h0 : p % 5 ≠ 0 := fun h => hpd (Nat.dvd_of_mod_eq_zero h)
  have h1 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have hq0 : (2 * p + 1) % 5 ≠ 0 := fun h => hqd (Nat.dvd_of_mod_eq_zero h)
  interval_cases h : (p % 5) <;> simp_all

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


import Mathlib

/-!
# Cousin Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.cousin_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Brockian.ConeLine

/-- Cousin primes `(p, p+4)` with `p > 5` travel exactly the roads
`2 → 1`, `3 → 2`, `4 → 3` on the five-ray wheel: `p % 5 ∈ {2,3,4}` and
`(p+4) % 5 = p % 5 - 1`. -/
theorem cousin_prime_roads {p : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime (p + 4))
    (h5 : 5 < p) :
    (p % 5, (p + 4) % 5) = (2, 1) ∨ (p % 5, (p + 4) % 5) = (3, 2) ∨
      (p % 5, (p + 4) % 5) = (4, 3) := by
  have hp0 : p % 5 ≠ 0 := by
    intro h
    have hdvd : 5 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases hp.eq_one_or_self_of_dvd 5 hdvd with h1 | h1 <;> omega
  have hq0 : (p + 4) % 5 ≠ 0 := by
    intro h
    have hdvd : 5 ∣ p + 4 := Nat.dvd_of_mod_eq_zero h
    rcases hq.eq_one_or_self_of_dvd 5 hdvd with h1 | h1 <;> omega
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


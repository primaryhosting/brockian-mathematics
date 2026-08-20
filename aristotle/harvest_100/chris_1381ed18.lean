import Mathlib

/-!
# Quadruplet Visits All Active Rays
Category: Cone Line
Target: Brockian.ConeLine.quadruplet_visits_all_active_rays
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`, i.e. `q % 5 ≠ 0`. -/
theorem mod_five_ne_zero_of_prime {q : ℕ} (hq : Nat.Prime q) (hq5 : 5 < q) :
    q % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero h
  have := (Nat.prime_dvd_prime_iff_eq (by norm_num) hq).mp hdvd
  omega

/-- A prime quadruplet `(p, p+2, p+6, p+8)` with `p > 5` visits all four active
residue rays mod `5` exactly once, in the order `(1, 3, 2, 4)`. -/
theorem quadruplet_visits_all_active_rays {p : ℕ} (hp : Nat.Prime p)
    (hp2 : Nat.Prime (p + 2)) (hp6 : Nat.Prime (p + 6)) (hp8 : Nat.Prime (p + 8))
    (hgt : 5 < p) :
    p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2 ∧ (p + 8) % 5 = 4 := by
  have h0 := mod_five_ne_zero_of_prime hp hgt
  have h2 := mod_five_ne_zero_of_prime hp2 (by omega)
  have h6 := mod_five_ne_zero_of_prime hp6 (by omega)
  have h8 := mod_five_ne_zero_of_prime hp8 (by omega)
  omega

end Brockian.ConeLine


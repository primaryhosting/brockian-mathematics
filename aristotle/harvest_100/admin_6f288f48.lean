/-
# Cousin Prime Roads
Category: Cone Line
Target: Brockian.ConeLine.cousin_prime_roads
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- A prime `p` greater than `5` is not divisible by `5`, i.e. `p % 5 ≠ 0`. -/
theorem mod_five_ne_zero_of_prime {p : ℕ} (hp : Nat.Prime p) (h5 : 5 < p) : p % 5 ≠ 0 := by
  intro h
  have hdvd : (5 : ℕ) ∣ p := Nat.dvd_of_mod_eq_zero h
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp 5 hdvd) with h1 | h1 <;> omega

/-- **Cousin prime roads.**  If `p` and `p + 4` are both prime and `p > 5`, then on the
five-ray wheel the pair `(p % 5, (p+4) % 5)` travels one of the roads `2 → 1`, `3 → 2`,
`4 → 3`. -/
theorem cousin_prime_roads {p : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime (p + 4))
    (h5 : 5 < p) :
    (p % 5, (p + 4) % 5) = (2, 1) ∨ (p % 5, (p + 4) % 5) = (3, 2) ∨
      (p % 5, (p + 4) % 5) = (4, 3) := by
  have h1 : p % 5 ≠ 0 := mod_five_ne_zero_of_prime hp h5
  have h2 : (p + 4) % 5 ≠ 0 := mod_five_ne_zero_of_prime hq (by omega)
  have h3 : p % 5 < 5 := Nat.mod_lt _ (by norm_num)
  have h4 : (p + 4) % 5 = (p % 5 + 4) % 5 := by omega
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


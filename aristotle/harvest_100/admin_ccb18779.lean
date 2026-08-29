/-
# Triplet Two Patterns
Category: Cone Line
Target: Brockian.ConeLine.triplet_two_patterns
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

namespace Brockian.ConeLine

/-- A prime `q > 5` is not divisible by `5`, i.e. `q % 5 ≠ 0`. -/
lemma mod_five_ne_zero_of_prime {q : ℕ} (hq : Nat.Prime q) (h : 5 < q) : q % 5 ≠ 0 := by
  intro hmod
  have hdvd : (5 : ℕ) ∣ q := Nat.dvd_of_mod_eq_zero hmod
  rcases (Nat.Prime.eq_one_or_self_of_dvd hq 5 hdvd) with h5 | h5 <;> omega

/-- A prime triplet `(p, p+2, p+6)` with `p > 5` has exactly two possible ray
patterns mod 5: `(1,3,2)` or `(2,4,3)`. -/
theorem triplet_two_patterns {p : ℕ} (hp : p.Prime) (hp2 : (p + 2).Prime)
    (hp6 : (p + 6).Prime) (h5 : 5 < p) :
    (p % 5 = 1 ∧ (p + 2) % 5 = 3 ∧ (p + 6) % 5 = 2) ∨
    (p % 5 = 2 ∧ (p + 2) % 5 = 4 ∧ (p + 6) % 5 = 3) := by
  have h0 : p % 5 ≠ 0 := mod_five_ne_zero_of_prime hp h5
  have h2 : (p + 2) % 5 ≠ 0 := mod_five_ne_zero_of_prime hp2 (by omega)
  have h6 : (p + 6) % 5 ≠ 0 := mod_five_ne_zero_of_prime hp6 (by omega)
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


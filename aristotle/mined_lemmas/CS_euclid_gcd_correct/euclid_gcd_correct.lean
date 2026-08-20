/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Euclid's algorithm, by repeated remainder.

The recursion terminates because the second argument strictly decreases at every
recursive call (`Nat.mod_lt`); this is exactly what the `termination_by` /
`decreasing_by` clauses certify, so `euclid` is a total function. -/

theorem euclid_gcd_correct (a b : Nat) :
    euclid a b = Nat.gcd a b ∧
      euclid a b ∣ a ∧ euclid a b ∣ b ∧
      ∀ c : Nat, c ∣ a → c ∣ b → c ∣ euclid a b := by
  refine ⟨euclid_eq_gcd a b, ?_, ?_, ?_⟩
  · rw [euclid_eq_gcd]; exact Nat.gcd_dvd_left a b
  · rw [euclid_eq_gcd]; exact Nat.gcd_dvd_right a b
  · intro c hca hcb
    rw [euclid_eq_gcd]
    exact Nat.dvd_gcd hca hcb

end CS

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


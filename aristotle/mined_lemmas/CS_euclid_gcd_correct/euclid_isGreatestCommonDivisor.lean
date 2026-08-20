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

namespace CS

/-- Euclid's algorithm, by repeated remainder.  The recursion is on the second
argument, which strictly decreases (`a % (b+1) < b+1`); Lean accepts the
definition precisely because this measure is well founded, so the algorithm
terminates on every input. -/

theorem euclid_isGreatestCommonDivisor (a b : Nat) :
    (euclid a b ∣ a ∧ euclid a b ∣ b) ∧ ∀ d : Nat, d ∣ a → d ∣ b → d ∣ euclid a b := by
  rw [euclid_gcd_correct]
  exact ⟨⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩, fun d ha hb => Nat.dvd_gcd ha hb⟩

end CS


/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Euclid's algorithm on the natural numbers: `euclid a b` repeatedly replaces
the pair `(a, b)` by `(b % a, a)` until the first component is `0`.

The definition is accepted by Lean only together with a termination proof: the
first argument strictly decreases at each recursive call, since `b % a < a`
whenever `a ≠ 0`. Hence `euclid` is a total function — the algorithm terminates
on every input. -/
def euclid (a b : Nat) : Nat :=
  if a = 0 then b else euclid (b % a) a
decreasing_by
  exact Nat.mod_lt _ (Nat.pos_of_ne_zero (by assumption))

@[simp] theorem euclid_zero_left (b : Nat) : euclid 0 b = b := by
  rw [euclid]; simp

/-- One step of the algorithm. -/
theorem euclid_of_ne_zero (a b : Nat) (h : a ≠ 0) : euclid a b = euclid (b % a) a := by
  rw [euclid]; simp [h]

/-- **Correctness of Euclid's algorithm**: for all natural numbers `a` and `b`,
the (terminating) algorithm `euclid` returns `gcd a b`. -/
theorem euclid_gcd_correct (a b : Nat) : euclid a b = Nat.gcd a b := by
  induction a, b using euclid.induct with
  | case1 b => simp
  | case2 a b h ih => rw [euclid_of_ne_zero a b h, Nat.gcd_rec, ih]

/-- The value returned by Euclid's algorithm is a greatest common divisor: it
divides both inputs, and every common divisor of the inputs divides it. -/
theorem euclid_spec (a b : Nat) :
    euclid a b ∣ a ∧ euclid a b ∣ b ∧ ∀ c : Nat, c ∣ a → c ∣ b → c ∣ euclid a b := by
  rw [euclid_gcd_correct]
  exact ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b, fun c => Nat.dvd_gcd⟩

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


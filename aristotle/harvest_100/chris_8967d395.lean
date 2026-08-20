/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Euclid's algorithm, by repeated remainders.  The definition is accepted by
Lean's termination checker (the second argument strictly decreases at each
recursive call), so the algorithm terminates on every input. -/
def euclid : Nat → Nat → Nat
  | a, 0 => a
  | a, b + 1 => euclid (b + 1) (a % (b + 1))
  decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

@[simp] theorem euclid_zero (a : Nat) : euclid a 0 = a := by
  rw [euclid]

theorem euclid_succ (a b : Nat) : euclid a (b + 1) = euclid (b + 1) (a % (b + 1)) := by
  rw [euclid]

/-- Euclid's algorithm computes the gcd. -/
theorem euclid_eq_gcd (a b : Nat) : euclid a b = Nat.gcd a b := by
  induction b using Nat.strongRecOn generalizing a with
  | _ b ih =>
    match b with
    | 0 => simp
    | (b + 1) =>
      rw [euclid_succ, ih (a % (b + 1)) (Nat.mod_lt _ (Nat.succ_pos b)),
        Nat.gcd_comm (b + 1) (a % (b + 1)), Nat.gcd_comm a (b + 1)]
      exact (Nat.gcd_rec (b + 1) a).symm

/-- **Correctness of Euclid's algorithm.**  The algorithm terminates on all
inputs (its recursive definition is total), and its result is a common divisor
of the two inputs that is divisible by every common divisor — i.e. it equals
`Nat.gcd a b`. -/
theorem euclid_gcd_correct (a b : Nat) :
    euclid a b = Nat.gcd a b ∧
    euclid a b ∣ a ∧ euclid a b ∣ b ∧
    ∀ d : Nat, d ∣ a → d ∣ b → d ∣ euclid a b := by
  refine ⟨euclid_eq_gcd a b, ?_, ?_, ?_⟩ <;> rw [euclid_eq_gcd]
  · exact Nat.gcd_dvd_left a b
  · exact Nat.gcd_dvd_right a b
  · exact fun d ha hb => Nat.dvd_gcd ha hb

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


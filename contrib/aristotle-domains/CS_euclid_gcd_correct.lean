/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Statement: Euclid's algorithm returns gcd(a,b) and terminates.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

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
def euclid : Nat → Nat → Nat
  | a, 0 => a
  | a, b + 1 => euclid (b + 1) (a % (b + 1))
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

@[simp] theorem euclid_zero (a : Nat) : euclid a 0 = a := by
  rw [euclid]

theorem euclid_succ (a b : Nat) : euclid a (b + 1) = euclid (b + 1) (a % (b + 1)) := by
  rw [euclid]

/-- The recursive step, stated for an arbitrary nonzero second argument. -/
theorem euclid_pos (a b : Nat) (hb : b ≠ 0) : euclid a b = euclid b (a % b) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  exact euclid_succ a c

/-- **Termination**: `euclid` is a total function on `ℕ × ℕ`, and each recursive
call strictly decreases the second argument, hence the algorithm halts. -/
theorem euclid_measure_decreases (a b : Nat) (hb : b ≠ 0) : a % b < b :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero hb)

/-- **Correctness**: Euclid's algorithm computes the greatest common divisor. -/
theorem euclid_gcd_correct (a b : Nat) : euclid a b = Nat.gcd a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    match b with
    | 0 => simp
    | (c + 1) =>
      rw [euclid_succ, ih _ (Nat.mod_lt _ (Nat.succ_pos c)), Nat.gcd_comm a (c + 1),
        Nat.gcd_rec (c + 1) a, Nat.gcd_comm]

/-- Correctness spelled out: `euclid a b` divides both arguments and is divisible
by every common divisor, i.e. it really is the greatest common divisor. -/
theorem euclid_isGreatestCommonDivisor (a b : Nat) :
    (euclid a b ∣ a ∧ euclid a b ∣ b) ∧ ∀ d : Nat, d ∣ a → d ∣ b → d ∣ euclid a b := by
  rw [euclid_gcd_correct]
  exact ⟨⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩, fun d ha hb => Nat.dvd_gcd ha hb⟩

end CS


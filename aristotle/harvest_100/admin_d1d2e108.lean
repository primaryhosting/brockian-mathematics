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
def euclid : Nat → Nat → Nat
  | a, 0 => a
  | a, (b + 1) => euclid (b + 1) (a % (b + 1))
  termination_by _ b => b
  decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

@[simp] theorem euclid_zero (a : Nat) : euclid a 0 = a := by
  rw [euclid]

theorem euclid_succ (a b : Nat) : euclid a (b + 1) = euclid (b + 1) (a % (b + 1)) := by
  rw [euclid]

/-- The termination measure of Euclid's algorithm: the second argument strictly
decreases at every recursive call. -/
theorem euclid_measure_decreasing (a b : Nat) (hb : 0 < b) : a % b < b :=
  Nat.mod_lt _ hb

/-- Euclid's algorithm computes `Nat.gcd`. -/
theorem euclid_eq_gcd (a b : Nat) : euclid a b = Nat.gcd a b := by
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    match b with
    | 0 => simp [Nat.gcd_zero_right]
    | (n + 1) =>
      rw [euclid_succ, ih (a % (n + 1)) (Nat.mod_lt _ (Nat.succ_pos n))]
      rw [Nat.gcd_comm (n + 1) (a % (n + 1)), ← Nat.gcd_rec (n + 1) a,
        Nat.gcd_comm (n + 1) a]

/-- **Correctness of Euclid's algorithm.**  For all naturals `a b`, the value
returned by `euclid a b` — a total function, since the recursion terminates: the
second argument strictly decreases at each step, see `euclid_measure_decreasing`
— equals `Nat.gcd a b`, is a common divisor of `a` and `b`, and is divisible by
every common divisor of `a` and `b`.

The divisibility facts come from the library lemmas `Nat.gcd_dvd_left`,
`Nat.gcd_dvd_right` and `Nat.dvd_gcd`. -/
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


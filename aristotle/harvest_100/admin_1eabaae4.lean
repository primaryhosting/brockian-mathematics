/-
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
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

/-- Euclid's algorithm: repeatedly replace `(a, b)` by `(b, a % b)` until the second
argument is `0`.  The recursion is well founded because the second argument strictly
decreases, so this definition is total (the algorithm terminates on all inputs). -/
def euclid (a b : ℕ) : ℕ :=
  if b = 0 then a else euclid b (a % b)
termination_by b
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero ‹b ≠ 0›)

/-- The measure used by Euclid's algorithm strictly decreases at each recursive call:
this is exactly the termination argument. -/
theorem euclid_measure_decreases (a b : ℕ) (hb : b ≠ 0) : a % b < b :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero hb)

@[simp] theorem euclid_zero (a : ℕ) : euclid a 0 = a := by
  rw [euclid]; simp

theorem euclid_succ (a b : ℕ) (hb : b ≠ 0) : euclid a b = euclid b (a % b) := by
  rw [euclid]; simp [hb]

/-- Euclid's algorithm computes the gcd. -/
theorem euclid_eq_gcd (a b : ℕ) : euclid a b = Nat.gcd a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; simp
    · rw [euclid_succ a b hb.ne', ih (a % b) (Nat.mod_lt _ hb),
        Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

/--
**Correctness and termination of Euclid's algorithm.**

`CS.euclid` is defined by well-founded recursion on its second argument, hence is a
total function: the algorithm terminates on every input (the measure `b` strictly
decreases at each recursive call, as recorded in the first component).  Its result is
the greatest common divisor of `a` and `b`: it divides both arguments and is divisible
by every common divisor, and it agrees with `Nat.gcd`.
-/
theorem euclid_gcd_correct :
    (∀ a b : ℕ, b ≠ 0 → a % b < b) ∧
    (∀ a b : ℕ, euclid a b = Nat.gcd a b) ∧
    (∀ a b : ℕ, euclid a b ∣ a) ∧
    (∀ a b : ℕ, euclid a b ∣ b) ∧
    (∀ a b d : ℕ, d ∣ a → d ∣ b → d ∣ euclid a b) := by
  refine ⟨euclid_measure_decreases, euclid_eq_gcd, ?_, ?_, ?_⟩
  · intro a b; rw [euclid_eq_gcd]; exact Nat.gcd_dvd_left a b
  · intro a b; rw [euclid_eq_gcd]; exact Nat.gcd_dvd_right a b
  · intro a b d ha hb; rw [euclid_eq_gcd]; exact Nat.dvd_gcd ha hb

end CS


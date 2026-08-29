/-
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
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

namespace CS

/-- Euclid's algorithm: repeatedly replace `(a, b)` by `(b, a % b)` until the second
component is `0`. -/
def euclid (a b : ℕ) : ℕ :=
  if _h : b = 0 then a else euclid b (a % b)
decreasing_by exact Nat.mod_lt _ (Nat.pos_of_ne_zero _h)

/-- One step of Euclid's algorithm, as a state transition on pairs. -/
def step (p : ℕ × ℕ) : ℕ × ℕ := (p.2, p.1 % p.2)

@[simp] theorem euclid_zero (a : ℕ) : euclid a 0 = a := by
  rw [euclid]; simp

theorem euclid_succ (a b : ℕ) (hb : b ≠ 0) : euclid a b = euclid b (a % b) := by
  rw [euclid]; simp [hb]

/-- Euclid's algorithm computes the `gcd`. -/
theorem euclid_eq_gcd (a b : ℕ) : euclid a b = Nat.gcd a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; simp
    · rw [euclid_succ a b hb.ne', ih (a % b) (Nat.mod_lt _ hb) b,
        Nat.gcd_comm b (a % b), ← Nat.gcd_rec, Nat.gcd_comm]

/-- Euclid's algorithm terminates: iterating `step` from `(a, b)` reaches a state whose
second component is `0`, and the first component of that state is the value returned by
`euclid`. -/
theorem euclid_terminates (a b : ℕ) :
    ∃ n : ℕ, (step^[n] (a, b)).2 = 0 ∧ (step^[n] (a, b)).1 = euclid a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    rcases Nat.eq_zero_or_pos b with hb | hb
    · subst hb; exact ⟨0, rfl, by simp⟩
    · obtain ⟨n, h1, h2⟩ := ih (a % b) (Nat.mod_lt _ hb) b
      refine ⟨n + 1, ?_, ?_⟩
      · rw [Function.iterate_succ_apply]
        simpa [step] using h1
      · rw [Function.iterate_succ_apply]
        simpa [step, euclid_succ a b hb.ne'] using h2

/-- **Correctness and termination of Euclid's algorithm.**
The value `euclid a b` is a common divisor of `a` and `b` which every common divisor
divides (i.e. it is the greatest common divisor), and the algorithm terminates: iterating
its one-step transition from `(a, b)` reaches, in finitely many steps, a state with second
component `0` whose first component is exactly `euclid a b`. -/
theorem euclid_gcd_correct (a b : ℕ) :
    (euclid a b ∣ a ∧ euclid a b ∣ b ∧
      ∀ d : ℕ, d ∣ a → d ∣ b → d ∣ euclid a b) ∧
    ∃ n : ℕ, (step^[n] (a, b)).2 = 0 ∧ (step^[n] (a, b)).1 = euclid a b := by
  refine ⟨⟨?_, ?_, ?_⟩, euclid_terminates a b⟩ <;> rw [euclid_eq_gcd]
  · exact Nat.gcd_dvd_left a b
  · exact Nat.gcd_dvd_right a b
  · exact fun d hda hdb => Nat.dvd_gcd hda hdb

end CS


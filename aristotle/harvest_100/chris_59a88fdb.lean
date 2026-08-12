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

/-- Euclid's algorithm on natural numbers, defined by structural recursion on the
second argument via the strictly decreasing measure `b`. -/
def euclid : ℕ → ℕ → ℕ
  | a, 0 => a
  | a, (b + 1) => euclid (b + 1) (a % (b + 1))
decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

/-- Termination witness: the recursive call of Euclid's algorithm strictly decreases
the measure (the second argument). -/
theorem euclid_measure_decreasing (a b : ℕ) (hb : b ≠ 0) : a % b < b :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero hb)

@[simp] theorem euclid_zero (a : ℕ) : euclid a 0 = a := by
  rw [euclid]

theorem euclid_succ (a b : ℕ) :
    euclid a (b + 1) = euclid (b + 1) (a % (b + 1)) := by
  rw [euclid]

/-- Euclid's algorithm computes the gcd. -/
theorem euclid_eq_gcd (a b : ℕ) : euclid a b = Nat.gcd a b := by
  induction b using Nat.strong_induction_on generalizing a with
  | _ b ih =>
    match b with
    | 0 => simp
    | (n + 1) =>
      rw [euclid_succ, ih (a % (n + 1)) (Nat.mod_lt _ (Nat.succ_pos n)),
        Nat.gcd_comm (n + 1) (a % (n + 1)), ← Nat.gcd_rec, Nat.gcd_comm]

/-- **Correctness and termination of Euclid's algorithm.**

`CS.euclid` is a total (hence everywhere-terminating) function: its recursive call
strictly decreases the measure `b`, as recorded by `euclid_measure_decreasing`.
Its output on `(a, b)` is a common divisor of `a` and `b` which is divisible by every
common divisor of `a` and `b`, i.e. it is `gcd a b`. -/
theorem euclid_gcd_correct (a b : ℕ) :
    euclid a b = Nat.gcd a b ∧
    euclid a b ∣ a ∧ euclid a b ∣ b ∧
    ∀ d : ℕ, d ∣ a → d ∣ b → d ∣ euclid a b := by
  have h : euclid a b = Nat.gcd a b := euclid_eq_gcd a b
  refine ⟨h, ?_, ?_, ?_⟩
  · rw [h]; exact Nat.gcd_dvd_left a b
  · rw [h]; exact Nat.gcd_dvd_right a b
  · intro d hda hdb; rw [h]; exact Nat.dvd_gcd hda hdb

end CS


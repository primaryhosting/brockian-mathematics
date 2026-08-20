/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: the requested header must be the very first thing in the file,
and Lean does not allow a module doc comment to precede `import` commands.  The
development below therefore uses only Lean core (`Nat.gcd` and its equations
`Nat.gcd_rec`, `Nat.gcd_dvd_left`, `Nat.gcd_dvd_right`, `Nat.dvd_gcd`), which is
available in every Mathlib file as well.
-/

namespace CS

/-- Euclid's algorithm on natural numbers, in its classical remainder form
`euclid a b = euclid b (a % b)` for `b ≠ 0` and `euclid a 0 = a`.

The recursion is well founded because the second argument strictly decreases
(`Nat.mod_lt`); Lean's acceptance of this definition as a *total* function is
exactly the statement that the algorithm terminates on all inputs. -/
def euclid : Nat → Nat → Nat
  | a, 0 => a
  | a, b + 1 => euclid (b + 1) (a % (b + 1))
  decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

/-- Termination measure: each recursive call strictly decreases the second
argument, so Euclid's algorithm terminates. -/
theorem euclid_measure_decreases (a b : Nat) (hb : b ≠ 0) : a % b < b :=
  Nat.mod_lt _ (Nat.pos_of_ne_zero hb)

@[simp] theorem euclid_zero (a : Nat) : euclid a 0 = a := by
  rw [euclid]

theorem euclid_succ (a b : Nat) : euclid a (b + 1) = euclid (b + 1) (a % (b + 1)) := by
  rw [euclid]

/-- The step equation of Euclid's algorithm in its usual form. -/
theorem euclid_step (a b : Nat) (hb : b ≠ 0) : euclid a b = euclid b (a % b) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  exact euclid_succ a c

/-- Euclid's algorithm computes `Nat.gcd`, via the library equation
`Nat.gcd_rec`. -/
theorem euclid_eq_gcd (a b : Nat) : euclid a b = Nat.gcd a b := by
  induction a, b using euclid.induct with
  | case1 a => simp
  | case2 a b ih =>
    rw [euclid_succ, ih, Nat.gcd_comm a (b + 1), Nat.gcd_rec (b + 1) a, Nat.gcd_comm]

/-- **Euclid's algorithm is correct and terminates.**

`euclid a b` is a total (hence everywhere-terminating) function, it is a common
divisor of `a` and `b`, every common divisor of `a` and `b` divides it, and it
agrees with `Nat.gcd a b`.  Together these say that Euclid's algorithm returns
the greatest common divisor of `a` and `b`. -/
theorem euclid_gcd_correct (a b : Nat) :
    euclid a b = Nat.gcd a b ∧
      euclid a b ∣ a ∧ euclid a b ∣ b ∧
        ∀ d : Nat, d ∣ a → d ∣ b → d ∣ euclid a b := by
  refine ⟨euclid_eq_gcd a b, ?_, ?_, ?_⟩ <;> rw [euclid_eq_gcd]
  · exact Nat.gcd_dvd_left a b
  · exact Nat.gcd_dvd_right a b
  · exact fun _ hda hdb => Nat.dvd_gcd hda hdb

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


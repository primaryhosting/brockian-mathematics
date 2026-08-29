/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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
argument is zero.  The `termination_by`/`decreasing_by` clauses below constitute a
proof that the algorithm terminates on every input: the second argument strictly
decreases in each recursive call (`Nat.mod_lt`), and `<` on `Nat` is well-founded. -/
def euclid : Nat → Nat → Nat
  | a, 0 => a
  | a, (b + 1) => euclid (b + 1) (a % (b + 1))
  termination_by _ b => b
  decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

@[simp] theorem euclid_zero (a : Nat) : euclid a 0 = a := by
  rw [euclid]

theorem euclid_succ (a b : Nat) : euclid a (b + 1) = euclid (b + 1) (a % (b + 1)) := by
  rw [euclid]

/-- The step equation of Euclid's algorithm for a nonzero second argument. -/
theorem euclid_pos (a b : Nat) (hb : b ≠ 0) : euclid a b = euclid b (a % b) := by
  cases b with
  | zero => exact absurd rfl hb
  | succ n => exact euclid_succ a n

/-- Euclid's algorithm computes the greatest common divisor. -/
theorem euclid_eq_gcd : ∀ a b : Nat, euclid a b = Nat.gcd a b
  | a, 0 => by simp
  | a, (b + 1) => by
      rw [euclid_succ, euclid_eq_gcd (b + 1) (a % (b + 1)), Nat.gcd_comm a (b + 1),
        Nat.gcd_rec (b + 1) a, Nat.gcd_comm]
  termination_by _ b => b
  decreasing_by exact Nat.mod_lt _ (Nat.succ_pos b)

/--
**Correctness and termination of Euclid's algorithm.**

The function `CS.euclid` is defined by well-founded recursion on its second argument
(so it terminates on all inputs — see the `termination_by`/`decreasing_by` clauses in
its definition), and its result is the greatest common divisor of the two inputs:
it divides both arguments, and every common divisor of the arguments divides it.
In particular `CS.euclid a b = Nat.gcd a b`.

The library results used are `Nat.gcd_rec`, `Nat.gcd_comm`, `Nat.gcd_dvd_left`,
`Nat.gcd_dvd_right` and `Nat.dvd_gcd`.
-/
theorem euclid_gcd_correct (a b : Nat) :
    euclid a b = Nat.gcd a b ∧
      euclid a b ∣ a ∧ euclid a b ∣ b ∧
      ∀ d : Nat, d ∣ a → d ∣ b → d ∣ euclid a b := by
  have h : euclid a b = Nat.gcd a b := euclid_eq_gcd a b
  refine ⟨h, ?_, ?_, ?_⟩
  · rw [h]; exact Nat.gcd_dvd_left a b
  · rw [h]; exact Nat.gcd_dvd_right a b
  · intro d hda hdb
    rw [h]; exact Nat.dvd_gcd hda hdb

end CS


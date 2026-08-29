/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-- **Euclid's algorithm.**  On input `(a, b)` it returns `b` when `a = 0`, and otherwise
recurses on `(b % a, a)`.  The recursion is well founded: the first argument strictly
decreases at every step (`b % (a+1) < a+1`), which is exactly the termination argument
discharged by `decreasing_by` below.  Consequently `euclid` is a total function, i.e. the
algorithm terminates on every input. -/
def euclid : Nat → Nat → Nat
  | 0, b => b
  | (a + 1), b => euclid (b % (a + 1)) (a + 1)
  decreasing_by exact Nat.mod_lt _ (Nat.succ_pos a)

/-- The termination measure of Euclid's algorithm: on a recursive call the first
argument strictly decreases.  Since `Nat` is well founded, the algorithm terminates. -/
theorem euclid_measure_decreases (a b : Nat) (ha : 0 < a) : b % a < a :=
  Nat.mod_lt _ ha

@[simp] theorem euclid_zero (b : Nat) : euclid 0 b = b := by
  rw [euclid.eq_def]

theorem euclid_succ (a b : Nat) : euclid (a + 1) b = euclid (b % (a + 1)) (a + 1) := by
  rw [euclid.eq_def]

/-- Euclid's algorithm computes the greatest common divisor. -/
theorem euclid_eq_gcd (a b : Nat) : euclid a b = Nat.gcd a b := by
  fun_induction euclid a b with
  | case1 b => rw [Nat.gcd_zero_left]
  | case2 n b ih => rw [ih]; exact (Nat.gcd_rec (n + 1) b).symm

/--
**Correctness (and termination) of Euclid's algorithm.**

`CS.euclid` is defined by well-founded recursion on its first argument, which strictly
decreases at each recursive call (see `CS.euclid_measure_decreases`); hence it is a
total function and the algorithm terminates on all inputs.

This theorem states that the value it returns really is `gcd a b`: it coincides with
`Nat.gcd a b`, it is a common divisor of `a` and `b`, and every common divisor of `a`
and `b` divides it — i.e. it is the greatest common divisor.
-/
theorem euclid_gcd_correct (a b : Nat) :
    euclid a b = Nat.gcd a b ∧
    (euclid a b ∣ a ∧ euclid a b ∣ b) ∧
    (∀ d : Nat, d ∣ a → d ∣ b → d ∣ euclid a b) := by
  refine ⟨euclid_eq_gcd a b, ⟨?_, ?_⟩, ?_⟩
  · rw [euclid_eq_gcd]; exact Nat.gcd_dvd_left a b
  · rw [euclid_eq_gcd]; exact Nat.gcd_dvd_right a b
  · intro d hda hdb
    rw [euclid_eq_gcd]
    exact Nat.dvd_gcd hda hdb

/-- Greatest also in the sense of the order: any common divisor of `a` and `b` is at most
`euclid a b`, provided `a` and `b` are not both zero. -/
theorem euclid_greatest (a b : Nat) (h : 0 < a ∨ 0 < b) (d : Nat)
    (hda : d ∣ a) (hdb : d ∣ b) : d ≤ euclid a b := by
  have hpos : 0 < euclid a b := by
    rw [euclid_eq_gcd]
    rcases h with h | h
    · exact Nat.gcd_pos_of_pos_left b h
    · exact Nat.gcd_pos_of_pos_right a h
  exact Nat.le_of_dvd hpos ((euclid_gcd_correct a b).2.2 d hda hdb)

end CS


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

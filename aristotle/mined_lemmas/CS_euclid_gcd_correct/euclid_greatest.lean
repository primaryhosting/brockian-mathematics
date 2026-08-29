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

theorem euclid_greatest (a b : Nat) (h : 0 < a ∨ 0 < b) (d : Nat)
    (hda : d ∣ a) (hdb : d ∣ b) : d ≤ euclid a b := by
  have hpos : 0 < euclid a b := by
    rw [euclid_eq_gcd]
    rcases h with h | h
    · exact Nat.gcd_pos_of_pos_left b h
    · exact Nat.gcd_pos_of_pos_right a h
  exact Nat.le_of_dvd hpos ((euclid_gcd_correct a b).2.2 d hda hdb)

end CS


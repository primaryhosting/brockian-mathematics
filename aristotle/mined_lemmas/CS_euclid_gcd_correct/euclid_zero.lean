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

@[simp] theorem euclid_zero (b : Nat) : euclid 0 b = b := by
  rw [euclid.eq_def]


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

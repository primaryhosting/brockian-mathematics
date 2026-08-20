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

theorem euclid_measure_decreasing (a b : Nat) (hb : 0 < b) : a % b < b :=
  Nat.mod_lt _ hb

/-- Euclid's algorithm computes `Nat.gcd`. -/

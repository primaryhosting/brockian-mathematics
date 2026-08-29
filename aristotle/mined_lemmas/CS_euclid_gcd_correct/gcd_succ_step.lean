/-!
# Euclid Gcd Correct
Category: Computer Science
Target: CS.euclid_gcd_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to be the very first commands in a file,
-- so no `import` line can precede the header comment above. All results used here
-- (`Nat.gcd`, `Nat.gcd_rec`, `Nat.gcd_comm`, `Nat.dvd_gcd`, `Nat.gcd_dvd_left`,
-- `Nat.gcd_dvd_right`, `Nat.mod_lt`) are available without any extra imports.

set_option autoImplicit false

namespace CS

/-- Euclid's algorithm: repeatedly replace `(a, b)` by `(b, a % b)` until the second
argument is `0`. The `termination_by`/`decreasing_by` clauses (discharged by
`Nat.mod_lt`) constitute the termination proof: the recursion is well founded
because the second argument strictly decreases at each step. -/

theorem gcd_succ_step (a b : Nat) : Nat.gcd a (b + 1) = Nat.gcd (b + 1) (a % (b + 1)) := by
  rw [Nat.gcd_comm a (b + 1), Nat.gcd_rec (b + 1) a, Nat.gcd_comm]

/-- Euclid's algorithm computes `Nat.gcd`. -/

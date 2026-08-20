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

theorem euclid_step (a b : Nat) (hb : b ≠ 0) : euclid a b = euclid b (a % b) := by
  obtain ⟨c, rfl⟩ : ∃ c, b = c + 1 := ⟨b - 1, by omega⟩
  exact euclid_succ a c

/-- Euclid's algorithm computes `Nat.gcd`, via the library equation
`Nat.gcd_rec`. -/

/-!
# Ladner
Category: Frontier Cs
Target: CS.ladner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This development is deliberately self-contained: the required header comment
above is a module docstring, and Lean only accepts a module docstring at the
very beginning of a file when the file has no `import` commands.  Everything
below therefore uses only the Lean 4 core library.
-/

namespace CS

open Classical

/-- A language: a set of (encoded) strings, i.e. a predicate on `Nat`. -/
abbrev Lang := Nat → Prop

/-! ## Classical helpers -/


def defeated (g : Nat → Nat) (n : Nat) : Prop :=
  (g n % 2 = 0 ∧ ∃ z, z ≤ clock n ∧ ¬ (dec (g n / 2) z = true ↔ (K z ∧ g z % 2 = 0))) ∨
  (g n % 2 = 1 ∧ ∃ z, z ≤ clock n ∧ red (g n / 2) z ≤ clock n ∧
      ¬ (K z ↔ (K (red (g n / 2) z) ∧ g (red (g n / 2) z) % 2 = 0)))

/-- Stage-by-stage approximation of the gap function: `fAux m` agrees with the
gap function on all inputs `≤ m`. -/

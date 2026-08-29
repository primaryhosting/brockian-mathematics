/-!
# Pigeonhole Hash
Category: Computer Science
Target: CS.pigeonhole_hash
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-
Note on imports: the required header comment must be the very first thing in this file,
and Lean does not allow an `import` command after a module doc comment, so this file is
kept import-free and self-contained.  A one-line Mathlib proof of the same statement
(using `Fintype.exists_ne_map_eq_of_card_lt`) is given in `RequestProject/CSMathlib.lean`.
-/

/-- Numerical form of the pigeonhole principle: a function `f : ℕ → ℕ` sending each of the
`n + 1` inputs `0, …, n` into `{0, …, n - 1}` takes the same value twice. -/

theorem pigeonhole_hash_mathlib (n : ℕ) (f : Fin (n + 1) → Fin n) :
    ∃ a b : Fin (n + 1), a ≠ b ∧ f a = f b := by
  obtain ⟨a, b, hab, h⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f (by simp)
  exact ⟨a, b, hab, h⟩

/-- General form: any function between finite types whose codomain is strictly smaller than
its domain has a collision. -/

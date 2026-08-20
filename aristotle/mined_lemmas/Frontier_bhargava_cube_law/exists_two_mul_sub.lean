/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Integral binary quadratic forms -/

/-- An integral binary quadratic form `A x^2 + B x y + C y^2`, recorded by its
coefficient triple `(A, B, C)`. -/
structure BQF where
  A : Int
  B : Int
  C : Int
deriving DecidableEq, Repr

namespace BQF

/-- Evaluation of a binary quadratic form. -/

theorem exists_two_mul_sub {u v w : Int} (h : u ^ 2 - v ^ 2 = 4 * w) :
    ∃ k : Int, v = u - 2 * k := by
  obtain ⟨m, hm⟩ : ∃ m : Int, u = 2 * m ∨ u = 2 * m + 1 := ⟨u / 2, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n : Int, v = 2 * n ∨ v = 2 * n + 1 := ⟨v / 2, by omega⟩
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> subst hm <;> subst hn
  · exact ⟨m - n, by omega⟩
  · exact absurd h (by grind)
  · exact absurd h (by grind)
  · exact ⟨m - n, by omega⟩

/-- Any two forms of the same discriminant with leading coefficient `1` are properly
equivalent: they all lie in the principal class of that discriminant. -/

/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- An integral binary quadratic form `A x² + B x y + C y²`. -/
structure BinaryQF where
  A : Int
  B : Int
  C : Int

namespace BinaryQF

/-- Evaluation of a binary quadratic form. -/

theorem Q1_eval (x y : Int) :
    K.Q1.eval x y =
      -((K.a * x - K.e * y) * (K.d * x - K.h * y)
        - (K.b * x - K.f * y) * (K.c * x - K.g * y)) := by
  simp only [Q1, BinaryQF.eval]; grind

/-- `Q₂` really is `-det(M₂ x - N₂ y)`. -/

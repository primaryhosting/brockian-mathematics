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

theorem Q2_eval (x y : Int) :
    K.Q2.eval x y =
      -((K.a * x - K.b * y) * (K.g * x - K.h * y)
        - (K.c * x - K.d * y) * (K.e * x - K.f * y)) := by
  simp only [Q2, BinaryQF.eval]; grind

/-- `Q₃` really is `-det(M₃ x - N₃ y)`. -/

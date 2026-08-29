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

theorem Q3_eval (x y : Int) :
    K.Q3.eval x y =
      -((K.a * x - K.c * y) * (K.f * x - K.h * y)
        - (K.e * x - K.g * y) * (K.b * x - K.d * y)) := by
  simp only [Q3, BinaryQF.eval]; grind

end Cube

/-- The three binary quadratic forms produced by a Bhargava cube always have the
same discriminant. -/

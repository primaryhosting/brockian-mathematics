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

def Q2 : BinaryQF :=
  ⟨K.c * K.e - K.a * K.g,
   K.a * K.h + K.b * K.g - K.c * K.f - K.d * K.e,
   K.d * K.f - K.b * K.h⟩

/-- The third form attached to a cube, `Q₃(x,y) = -det(M₃ x - N₃ y)`. -/

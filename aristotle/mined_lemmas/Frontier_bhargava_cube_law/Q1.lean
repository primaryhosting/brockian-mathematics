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

def Q1 : BinaryQF :=
  ⟨K.b * K.c - K.a * K.d,
   K.a * K.h + K.d * K.e - K.b * K.g - K.c * K.f,
   K.f * K.g - K.e * K.h⟩

/-- The second form attached to a cube, `Q₂(x,y) = -det(M₂ x - N₂ y)`. -/

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

def Q3 : BinaryQF :=
  ⟨K.b * K.e - K.a * K.f,
   K.a * K.h + K.c * K.f - K.b * K.g - K.d * K.e,
   K.d * K.g - K.c * K.h⟩

/-- `Q₁` really is `-det(M₁ x - N₁ y)`. -/

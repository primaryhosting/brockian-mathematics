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

def form3 (K : Cube) : BQF := negDetForm K.a K.c K.e K.g K.b K.d K.f K.h

end Cube

/-- **The three binary quadratic forms of a Bhargava cube have equal discriminant.**
This common value is the discriminant of the cube. -/

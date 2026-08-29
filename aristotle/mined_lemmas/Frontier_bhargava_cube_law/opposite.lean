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

def opposite (q : BinaryQF) : BinaryQF := ⟨q.A, -q.B, q.C⟩

end BinaryQF

/-- A **Bhargava cube**: eight integers placed at the vertices of a cube.
With this labelling, the three ways of slicing the cube into a pair of `2 × 2`
matrices are
`(M₁, N₁) = ([[a,b],[c,d]], [[e,f],[g,h]])`,
`(M₂, N₂) = ([[a,c],[e,g]], [[b,d],[f,h]])`,
`(M₃, N₃) = ([[a,e],[b,f]], [[c,g],[d,h]])`. -/
structure Cube where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int
  g : Int
  h : Int

namespace Cube

variable (K : Cube)

/-- The first form attached to a cube, `Q₁(x,y) = -det(M₁ x - N₁ y)`. -/

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

theorem negDetForm_eval (m11 m12 m21 m22 n11 n12 n21 n22 x y : Int) :
    (negDetForm m11 m12 m21 m22 n11 n12 n21 n22).eval x y
      = -((m11 * x + n11 * y) * (m22 * x + n22 * y)
          - (m12 * x + n12 * y) * (m21 * x + n21 * y)) := by
  simp only [BQF.eval, negDetForm]
  grind

namespace Cube

/-- The first form of a cube: slice into the faces `M₁ = (a b ; c d)`,
`N₁ = (e f ; g h)` and take `-det (M₁ x + N₁ y)`. -/

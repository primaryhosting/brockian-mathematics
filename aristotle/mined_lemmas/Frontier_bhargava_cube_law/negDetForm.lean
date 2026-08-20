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

def negDetForm (m11 m12 m21 m22 n11 n12 n21 n22 : Int) : BQF :=
  ⟨-(m11 * m22 - m12 * m21),
   -(m11 * n22 + n11 * m22 - m12 * n21 - n12 * m21),
   -(n11 * n22 - n12 * n21)⟩

/-- `negDetForm` really is the form `(x, y) ↦ -det (M x + N y)`. -/

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

@[simp] theorem disc_op (Q : BQF) : Q.op.disc = Q.disc := by
  simp only [disc, op_A, op_B, op_C]
  grind

end BQF

/-! ## Bhargava cubes and their three binary quadratic forms -/

/-- A *Bhargava cube*: a `2 × 2 × 2` array of integers.  With Bhargava's labelling the
eight entries sit at the vertices of a cube, the front face being `a b / c d` and the
back face `e f / g h`. -/
structure Cube where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int
  g : Int
  h : Int
deriving DecidableEq, Repr

/-- `negDetForm` is the binary quadratic form `-det (M x + N y)` attached to a pair of
`2 × 2` matrices `M = (m11 m12 ; m21 m22)` and `N = (n11 n12 ; n21 n22)`. -/

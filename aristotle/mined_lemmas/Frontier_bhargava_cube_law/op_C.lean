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

@[simp] theorem op_C (Q : BQF) : Q.op.C = Q.C := rfl


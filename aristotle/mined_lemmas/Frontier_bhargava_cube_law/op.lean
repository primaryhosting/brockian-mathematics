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

def op (Q : BQF) : BQF := ⟨Q.A, -Q.B, Q.C⟩

/-- Proper (i.e. `SL₂(ℤ)`-) equivalence of binary quadratic forms: `Q'` is obtained
from `Q` by a substitution of determinant `1`.  The classes of this relation are the
elements of the form class group. -/

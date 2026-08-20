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

@[simp] theorem form3_cubeOfForm (A B C : Int) :
    (cubeOfForm A B C).form3 = (⟨A, B, C⟩ : BQF).op := by
  simp only [Cube.form3, cubeOfForm, negDetForm, BQF.op, BQF.mk.injEq]
  grind

/-- The Gauss composition identity in the base case: the principal form
`x² - B x y + A C y²` composed with `Q = (A, B, C)` gives back `Q`, via an explicit
integral bilinear substitution (the multiplication map of the corresponding ideals). -/

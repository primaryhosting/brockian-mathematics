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

theorem cube_disc_eq (K : Cube) :
    K.form1.disc = K.form2.disc ∧ K.form2.disc = K.form3.disc := by
  constructor <;>
    · simp only [Cube.form1, Cube.form2, Cube.form3, negDetForm, BQF.disc]
      grind

/-! ## The principal class -/

/-- If `u^2 - v^2` is divisible by `4` then `u` and `v` have the same parity. -/

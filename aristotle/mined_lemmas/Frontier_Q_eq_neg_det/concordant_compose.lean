/-
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- A Bhargava cube: a `2 × 2 × 2` array of integers.  We label the eight entries as in
Bhargava's *Higher composition laws I*: the front face is `a b / c d` and the back face is
`e f / g h`. -/
structure Cube where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  g : ℤ
  h : ℤ
  deriving DecidableEq

/-- An integral binary quadratic form `A x² + B x y + C y²`, recorded by its coefficients. -/
structure QF where
  A : ℤ
  B : ℤ
  C : ℤ
  deriving DecidableEq

namespace QF

/-- Evaluation of a binary quadratic form. -/

theorem concordant_compose (A₁ A₂ B C x₁ y₁ x₂ y₂ : ℤ) :
    (QF.mk A₁ B (A₂ * C)).eval x₁ y₁ * (QF.mk A₂ B (A₁ * C)).eval x₂ y₂ =
      (QF.mk (A₁ * A₂) B C).eval (x₁ * x₂ - C * y₁ * y₂)
        (A₁ * x₁ * y₂ + A₂ * x₂ * y₁ + B * y₁ * y₂) := by
  simp only [QF.eval]
  ring

/--
**Bhargava's cube law (base case).**

For every Bhargava cube the three binary quadratic forms `Q₁, Q₂, Q₃` obtained from the three
slicings have the same discriminant; and for the concordant cube `concordantCube A₁ A₂ B C` the
three forms are exactly `A₁x² + Bxy + A₂Cy²`, `A₂x² + Bxy + A₁Cy²` and the opposite of
`A₁A₂x² + Bxy + Cy²`, and the product of the first two forms is represented by that third form
through an explicit pair of bilinear substitutions — i.e. `Q₁ ∘ Q₂ ∘ Q₃` is the principal class,
which is Gauss composition in Dirichlet's classical form.
-/

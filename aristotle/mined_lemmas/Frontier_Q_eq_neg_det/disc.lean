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

def disc (q : QF) : ℤ := q.B ^ 2 - 4 * q.A * q.C

/-- The opposite (inverse) form `A x² - B x y + C y²`; it represents the inverse class. -/

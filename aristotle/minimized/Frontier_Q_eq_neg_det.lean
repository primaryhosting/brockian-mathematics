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

def eval (q : QF) (x y : ℤ) : ℤ := q.A * x ^ 2 + q.B * x * y + q.C * y ^ 2

/-- The discriminant `B² - 4AC`. -/

def M₁ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.b; K.c, K.d]
/-- First slicing, back face. -/

def N₁ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.e, K.f; K.g, K.h]
/-- Second slicing, first slice. -/

def M₂ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.c; K.e, K.g]
/-- Second slicing, second slice. -/

def N₂ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.b, K.d; K.f, K.h]
/-- Third slicing, first slice. -/

def M₃ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.e; K.b, K.f]
/-- Third slicing, second slice. -/

def N₃ (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.c, K.g; K.d, K.h]

/-- The first form of the cube, `Q₁(x,y) = -det(M₁ x + N₁ y)`. -/

def Q₁ (K : Cube) : QF :=
  ⟨-(K.a * K.d - K.b * K.c),
   -(K.a * K.h + K.d * K.e - K.b * K.g - K.c * K.f),
   -(K.e * K.h - K.f * K.g)⟩

/-- The second form of the cube, `Q₂(x,y) = -det(M₂ x + N₂ y)`. -/

def Q₂ (K : Cube) : QF :=
  ⟨-(K.a * K.g - K.c * K.e),
   -(K.a * K.h + K.b * K.g - K.c * K.f - K.d * K.e),
   -(K.b * K.h - K.d * K.f)⟩

/-- The third form of the cube, `Q₃(x,y) = -det(M₃ x + N₃ y)`. -/

def Q₃ (K : Cube) : QF :=
  ⟨-(K.a * K.f - K.b * K.e),
   -(K.a * K.h + K.c * K.f - K.d * K.e - K.b * K.g),
   -(K.c * K.h - K.d * K.g)⟩

lemma Q₁_eq_neg_det (K : Cube) (x y : ℤ) :
    K.Q₁.eval x y = -(x • K.M₁ + y • K.N₁).det := by
  simp [QF.eval, Q₁, M₁, N₁, Matrix.det_fin_two]
  ring

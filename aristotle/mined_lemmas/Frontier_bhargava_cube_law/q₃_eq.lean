/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 does not allow an `import` command to follow a module docstring,
so in order to begin the file with exactly the header comment requested, this development is
self-contained and uses only the Lean core prelude (no Mathlib).  A search of Mathlib turns up
no Bhargava cubes, no Gauss/Dirichlet composition of binary quadratic forms, and no class group
of binary quadratic forms, so there is no existing lemma to cite here; the `2 × 2` determinants
and binary quadratic forms used below are defined from scratch.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## `2 × 2` integer matrices -/

/-- A `2 × 2` integer matrix `!![a, b; c, d]`. -/
structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq

namespace Mat2

/-- The determinant `ad - bc`. -/

theorem q₃_eq (x y : Int) : K.q₃ x y = K.Q₃.eval x y := by
  simp only [q₃, Q₃, BQF.eval, M₃, N₃, Mat2.det, Mat2.sub_a, Mat2.sub_b, Mat2.sub_c, Mat2.sub_d,
    Mat2.smul_a, Mat2.smul_b, Mat2.smul_c, Mat2.smul_d]
  grind

/-- **All three quadratic forms of a Bhargava cube have the same discriminant** — the common
value being (minus) the hyperdeterminant of the cube.  This is what makes the cube law a
composition law on forms of a fixed discriminant. -/

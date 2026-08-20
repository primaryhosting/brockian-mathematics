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

@[simp] theorem smul_d (x : Int) (M : Mat2) : (x * M).d = x * M.d := rfl

end Mat2

/-! ## Integral binary quadratic forms -/

/-- An integral binary quadratic form `a x² + b x y + c y²`, recorded by its coefficients. -/
structure BQF where
  a : Int
  b : Int
  c : Int
  deriving DecidableEq

namespace BQF

/-- Evaluation of a binary quadratic form at `(x, y)`. -/

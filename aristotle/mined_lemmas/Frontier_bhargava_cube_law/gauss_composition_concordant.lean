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

theorem gauss_composition_concordant (a₁ a₂ B C x₁ y₁ x₂ y₂ : Int) :
    (BQF.mk a₁ B (a₂ * C)).eval x₁ y₁ * (BQF.mk a₂ B (a₁ * C)).eval x₂ y₂
      = (BQF.mk (a₁ * a₂) B C).eval (x₁ * x₂ - C * y₁ * y₂)
          (a₁ * x₁ * y₂ + a₂ * x₂ * y₁ + B * y₁ * y₂) := by
  simp only [BQF.eval]
  grind

/-- **Bhargava's cube law (base case).**

Part 1 (well-definedness of the law).  For every `2 × 2 × 2` integer cube `K`, the three
slicings produce binary quadratic forms `Qᵢ(x, y) = -det(Mᵢ x - Nᵢ y)`, whose coefficient
triples are the ones recorded in `K.Q₁`, `K.Q₂`, `K.Q₃`, and all three forms have one and the
same discriminant.  So a cube really does determine a triple of forms of a fixed discriminant.

Part 2 (the law recovers Gauss composition).  For the cube
`K = (a = 0, b = a₁, c = a₂, d = B, e = 1, f = 0, g = 0, h = -C)`
the three forms are explicitly `Q₁ = (a₁a₂, B, C)`, `Q₂ = (a₂, -B, a₁C)`, `Q₃ = (a₁, -B, a₂C)`,
all of discriminant `B² - 4a₁a₂C`, and they satisfy the composition identity
`Q₃(x₁, y₁) · Q₂(x₂, y₂) = Q₁(X, Y)` for an explicit bilinear substitution.  Since `Q₂` and `Q₃`
are `(a₂, B, a₁C)` and `(a₁, B, a₂C)` after the change of variables `y ↦ -y`, this is precisely
Dirichlet's composition of the concordant forms `(a₁, B, a₂C)` and `(a₂, B, a₁C)` into
`(a₁a₂, B, C)`, i.e. Gauss composition; equivalently `[Q₁][Q₂][Q₃] = 1` in the form class group.
-/

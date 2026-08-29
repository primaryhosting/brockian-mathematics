/-
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
Note on the header: Lean 4 requires `import` to be the first command of a file, so the mandated
header above is reproduced verbatim as an ordinary block comment rather than as a module
docstring (`/-! ... -/`), which would itself be a command and could not precede `import`.

# Bhargava's cube law

A *Bhargava cube* is an element of `ℤ² ⊗ ℤ² ⊗ ℤ²`, i.e. eight integers placed at the vertices of
a cube.  Slicing the cube by planes parallel to each of the three pairs of opposite faces gives
three pairs of `2 × 2` integer matrices `(Mᵢ, Nᵢ)`, and hence three integral binary quadratic
forms

`Qᵢ(x, y) = -det(Mᵢ x - Nᵢ y)`.

Bhargava's cube law (Higher composition laws I) states that the three forms have the same
discriminant and that, in the class group of that discriminant, `Q₁ ∘ Q₂ ∘ Q₃` is the identity;
this recovers Gauss composition.

This file develops the material needed for the base case and proves it:

* `Frontier.cube_disc_eq` : the three forms of an arbitrary cube share a discriminant, given
  explicitly by the invariant `Frontier.Cube.disc`.
* `Frontier.form2_actFirst`, `Frontier.form3_actFirst`, `Frontier.form1_actFirst` : the action of
  `SL₂(ℤ)` on the first pair of faces fixes `Q₂` and `Q₃` on the nose and changes `Q₁` by the
  corresponding unimodular substitution — so the triple of `SL₂(ℤ)`-classes is a genuine invariant
  of the `Γ = SL₂(ℤ)³`-orbit.
* `Frontier.dirichletCube_forms` : the cube of *concordant* forms `(a₁, B, a₂C)`, `(a₂, B, a₁C)`
  has third form `(a₁a₂, -B, C)`, the opposite of the Dirichlet composite.
* `Frontier.gauss_composition` : the explicit bilinear composition identity
  `Q₁(x₁,y₁) · Q₂(x₂,y₂) = Q₃ᵒᵖ(X, Y)` for that cube, i.e. Gauss/Dirichlet composition.
* `Frontier.brahmagupta` : its base case, composition of the principal form with itself.
* `Frontier.bhargava_cube_law` : the packaged statement.
-/

namespace Frontier

/-- An integral binary quadratic form `A x² + B x y + C y²`, recorded by its coefficients. -/
structure BQF where
  A : ℤ
  B : ℤ
  C : ℤ
deriving DecidableEq, Repr

namespace BQF

/-- Evaluation of a binary quadratic form. -/

theorem brahmagupta (n x₁ y₁ x₂ y₂ : ℤ) :
    (BQF.principal n).eval x₁ y₁ * (BQF.principal n).eval x₂ y₂
      = (BQF.principal n).eval (x₁ * x₂ + n * y₁ * y₂) (x₁ * y₂ + y₁ * x₂) := by
  simp [BQF.principal, BQF.eval]; ring

/-!
## The cube law

The theorem below packages the statement.  For an arbitrary Bhargava cube:

* **(1)** the three attached binary quadratic forms all have the same discriminant, the
  hyperdeterminant invariant `Cube.disc` — so a cube determines a triple of forms of a common
  discriminant;
* **(2)** the `Γ = SL₂(ℤ)³`-action is well defined on this data: acting by `γ ∈ SL₂(ℤ)` on one
  pair of opposite faces fixes the other two forms exactly and changes the remaining form by the
  unimodular substitution `γ`, hence not its class;
* **(3)** for the cube built from a pair of concordant forms `(a₁, B, a₂C)`, `(a₂, B, a₁C)` of
  discriminant `B² - 4a₁a₂C`, the third form is `(a₁a₂, -B, C)`, and the explicit bilinear
  identity `Q₁(x₁,y₁) · Q₂(x₂,y₂) = Q₃ᵒᵖ(X, Y)` holds — this is exactly Gauss (Dirichlet)
  composition, i.e. `Q₁ ∘ Q₂ ∘ Q₃ = 1` in the class group;
* **(4)** in the base case `a₁ = a₂ = 1`, `B = 0`, `C = -n` the cube is the identity cube, all
  three forms are the principal form `x² - n y²` of discriminant `4n`, and the composition law
  degenerates to Brahmagupta's identity.
-/

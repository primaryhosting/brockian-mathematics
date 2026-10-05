import Mathlib

/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Integral binary quadratic forms -/

/-- An integral binary quadratic form `A x² + B x y + C y²`, recorded by its coefficients. -/
structure BQF where
  /-- Coefficient of `x²`. -/
  A : ℤ
  /-- Coefficient of `x y`. -/
  B : ℤ
  /-- Coefficient of `y²`. -/
  C : ℤ
  deriving DecidableEq

namespace BQF

/-- Evaluation of a binary quadratic form. -/

def composeY (a1 a2 b : ℤ) (x1 y1 x2 y2 : ℤ) : ℤ :=
  a1 * (x1 * y2) + a2 * (x2 * y1) + b * (y1 * y2)

/-! ## The cube law -/

/--
**Bhargava's cube law (base case).**

For the concordant cube `K = concordantCube a₁ a₂ b c` attached to arbitrary integers
`a₁, a₂, b, c`:

* its three quadratic forms are exactly `Q₁ = (a₁, b, a₂c)`, `Q₂ = (a₂, b, a₁c)` and
  `Q₃ = (a₁a₂, -b, c)`, the last being the *opposite* (i.e. class-group inverse) of the
  Gauss composite `Q₁ ∘ Q₂ = (a₁a₂, b, c)`;
* all three forms have the same discriminant `b² - 4a₁a₂c` (this holds for *every* cube,
  see `Frontier.Cube.disc_Q1_eq_disc_Q2`);
* the classical Gauss/Dirichlet composition identity holds:
  `Q₁(x₁,y₁) · Q₂(x₂,y₂) = (Q₁ ∘ Q₂)(X, Y)` with `X, Y` the explicit bilinear forms
  `composeX`, `composeY`.

Together these say that `Q₁ · Q₂ · Q₃ = 1` in the class group of forms of discriminant
`b² - 4a₁a₂c`, i.e. the cube law recovers Gauss composition.
-/

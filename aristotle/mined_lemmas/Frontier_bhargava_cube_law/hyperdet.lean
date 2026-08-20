import Mathlib

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

/-!
# Bhargava's cube law

A *Bhargava cube* is a `2 × 2 × 2` array of integers

```
        e ------- f
       /|        /|
      a ------- b |
      | g ------|-h
      |/        |/
      c ------- d
```

Slicing the cube in each of the three coordinate directions produces three pairs of
`2 × 2` integer matrices `(M₁, N₁)`, `(M₂, N₂)`, `(M₃, N₃)`:

* `M₁ = ![![a, b], ![c, d]]`, `N₁ = ![![e, f], ![g, h]]`,
* `M₂ = ![![a, c], ![e, g]]`, `N₂ = ![![b, d], ![f, h]]`,
* `M₃ = ![![a, e], ![b, f]]`, `N₃ = ![![c, g], ![d, h]]`,

and each pair yields an integral binary quadratic form

`Qᵢ(x, y) = - det (x · Mᵢ - y · Nᵢ)`.

Bhargava's cube law states that these three forms all have the same discriminant `D`
(namely Cayley's hyperdeterminant of the cube) and that their classes compose to the
identity in the form class group of discriminant `D`, i.e. `[Q₁] [Q₂] [Q₃] = 1`; this
recovers Gauss composition.

This file proves, over `ℤ` and for an *arbitrary* cube:

* `Frontier.Cube.disc_Q₁`, `disc_Q₂`, `disc_Q₃`: each `disc Qᵢ` equals the hyperdeterminant,
  hence the three discriminants agree (`Frontier.Cube.disc_eq`);
* the concrete Gauss composition identities
  `Frontier.Cube.comp₁₂`, `comp₂₃`, `comp₃₁`, e.g.
  `Q₁(x₁,y₁) * Q₂(x₂,y₂) = Q₃⁻¹(X, Y)` for explicit bilinear `X`, `Y` built from the cube
  entries, where `Q₃⁻¹ = (A₃, -B₃, C₃)` is the form representing the inverse class of `[Q₃]`.
  This is exactly the statement `[Q₁][Q₂] = [Q₃]⁻¹`, i.e. `[Q₁][Q₂][Q₃] = 1`, in its
  effective (bilinear-identity) form;
* the base case recovering classical **Dirichlet/Gauss composition**: the cube
  `Frontier.dirichletCube a₁ a₂ m n` has slices `(a₁, m, a₂n)`, `(a₂, m, a₁n)`,
  `(a₁a₂, -m, n)`, and the composition identity specializes to Dirichlet's classical
  formula composing `(a₁, m, a₂n)` and `(a₂, m, a₁n)` into `(a₁a₂, m, n)`.

The main bundled statement is `Frontier.bhargava_cube_law`.
-/

namespace Frontier

/-- An integral binary quadratic form `A x² + B x y + C y²`, recorded by its coefficients. -/
structure BQF where
  /-- coefficient of `x²` -/
  A : ℤ
  /-- coefficient of `x y` -/
  B : ℤ
  /-- coefficient of `y²` -/
  C : ℤ
  deriving DecidableEq, Repr

namespace BQF

/-- Evaluation of a binary quadratic form. -/

def hyperdet : ℤ :=
  K.a ^ 2 * K.h ^ 2 + K.b ^ 2 * K.g ^ 2 + K.c ^ 2 * K.f ^ 2 + K.d ^ 2 * K.e ^ 2
    - 2 * (K.a * K.b * K.g * K.h + K.a * K.c * K.f * K.h + K.a * K.d * K.e * K.h
        + K.b * K.c * K.f * K.g + K.b * K.d * K.e * K.g + K.c * K.d * K.e * K.f)
    + 4 * (K.a * K.d * K.f * K.g + K.b * K.c * K.e * K.h)

/-! ### The forms really are `-det (x Mᵢ - y Nᵢ)` -/


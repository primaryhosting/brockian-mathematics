/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-!
## Bhargava cubes and their three binary quadratic forms

A *Bhargava cube* is a `2 × 2 × 2` array of integers

```
      e ------- f
     /|        /|
    a ------- b |
    | |       | |
    | g ------| h
    |/        |/
    c ------- d
```

There are three ways of slicing the cube into a pair of `2 × 2` matrices `(M, N)`:

* front/back:   `M₁ = ![![a, b], ![c, d]]`,  `N₁ = ![![e, f], ![g, h]]`;
* top/bottom:   `M₂ = ![![a, c], ![e, g]]`,  `N₂ = ![![b, d], ![f, h]]`;
* left/right:   `M₃ = ![![a, e], ![b, f]]`,  `N₃ = ![![c, g], ![d, h]]`.

Each slicing produces a binary quadratic form `Qᵢ(x, y) = -det(Mᵢ x - Nᵢ y)`.

Bhargava's *cube law* asserts that these three forms all have the same discriminant `D`
and that their classes compose to the identity in the class group of forms of
discriminant `D`, thereby recovering Gauss composition.

This file
* defines cubes and the three associated forms,
* proves the discriminant identity `Disc Q₁ = Disc Q₂ = Disc Q₃` for **every** cube, and
* proves the base case of the cube law: for the cube whose first slicing yields the
  *principal* form, the law becomes an explicit bilinear Gauss-composition identity
  `Q₂(x₁,y₁) · Q₃(x₂,y₂) = Q₁(L₁, L₂)`.
-/

/-- A Bhargava cube: a `2 × 2 × 2` array of integers. -/
structure Cube where
  /-- vertex `(0,0,0)` -/ a : ℤ
  /-- vertex `(0,0,1)` -/ b : ℤ
  /-- vertex `(0,1,0)` -/ c : ℤ
  /-- vertex `(0,1,1)` -/ d : ℤ
  /-- vertex `(1,0,0)` -/ e : ℤ
  /-- vertex `(1,0,1)` -/ f : ℤ
  /-- vertex `(1,1,0)` -/ g : ℤ
  /-- vertex `(1,1,1)` -/ h : ℤ
  deriving DecidableEq, Repr

namespace Cube

variable (K : Cube)

/-- The first form of a cube, `Q₁(x,y) = -det(M₁ x - N₁ y)` with
`M₁ = ![![a, b], ![c, d]]` and `N₁ = ![![e, f], ![g, h]]`. -/

lemma baseCube_disc (A C f g : ℤ) :
    disc (baseCube A C f g).Q₁ = (g - f) ^ 2 - 4 * A * C ∧
    disc (baseCube A C f g).Q₂ = (g - f) ^ 2 - 4 * A * C ∧
    disc (baseCube A C f g).Q₃ = (g - f) ^ 2 - 4 * A * C := by
  refine ⟨?_, ?_, ?_⟩ <;> · simp only [disc, baseCube_Q₁, baseCube_Q₂, baseCube_Q₃]; ring

/-- **Bhargava's cube law (base case).**

For the Bhargava cube `baseCube A C f g = (0, 1, 1, 0, A, f, g, -C)`:

* the three associated binary quadratic forms `Q₁, Q₂, Q₃` all have the same
  discriminant `D = (g - f)² - 4AC`;
* `Q₁` is the principal form of discriminant `D` (it represents `1`), while
  `Q₂ = A x² + B x y + C y²` (with `B = g - f`) is an arbitrary form of discriminant `D`
  and `Q₃` is its opposite;
* the classes of the three forms compose to the identity: this is witnessed by the
  explicit Gauss-composition identity
  `Q₂(x₁,y₁) · Q₃(x₂,y₂) = Q₁(L₁, L₂)`
  for the integral bilinear forms
  `L₁ = A x₁x₂ + f x₁y₂ + g x₂y₁ - C y₁y₂` and `L₂ = x₁y₂ + x₂y₁`.

This is exactly Gauss composition of a form with its opposite, yielding the principal
class, i.e. the base case of the composition law induced by Bhargava's cube. -/

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
def Q₁ (x y : ℤ) : ℤ :=
  -((K.a * x - K.e * y) * (K.d * x - K.h * y) - (K.b * x - K.f * y) * (K.c * x - K.g * y))

/-- The second form of a cube, `Q₂(x,y) = -det(M₂ x - N₂ y)` with
`M₂ = ![![a, c], ![e, g]]` and `N₂ = ![![b, d], ![f, h]]`. -/
def Q₂ (x y : ℤ) : ℤ :=
  -((K.a * x - K.b * y) * (K.g * x - K.h * y) - (K.c * x - K.d * y) * (K.e * x - K.f * y))

/-- The third form of a cube, `Q₃(x,y) = -det(M₃ x - N₃ y)` with
`M₃ = ![![a, e], ![b, f]]` and `N₃ = ![![c, g], ![d, h]]`. -/
def Q₃ (x y : ℤ) : ℤ :=
  -((K.a * x - K.c * y) * (K.f * x - K.h * y) - (K.e * x - K.g * y) * (K.b * x - K.d * y))

end Cube

/-- The discriminant `B² - 4AC` of a binary quadratic form `Q(x,y) = A x² + B x y + C y²`,
read off from the values of `Q` at `(1,0)`, `(0,1)` and `(1,1)`. -/
def disc (Q : ℤ → ℤ → ℤ) : ℤ :=
  (Q 1 1 - Q 1 0 - Q 0 1) ^ 2 - 4 * Q 1 0 * Q 0 1

namespace Cube

variable (K : Cube)

lemma disc_Q₁ :
    disc K.Q₁ = (K.a * K.h + K.d * K.e - K.b * K.g - K.c * K.f) ^ 2
      - 4 * (K.a * K.d - K.b * K.c) * (K.e * K.h - K.f * K.g) := by
  simp only [disc, Q₁]; ring

lemma disc_Q₂ :
    disc K.Q₂ = (K.a * K.h + K.b * K.g - K.c * K.f - K.d * K.e) ^ 2
      - 4 * (K.a * K.g - K.c * K.e) * (K.b * K.h - K.d * K.f) := by
  simp only [disc, Q₂]; ring

lemma disc_Q₃ :
    disc K.Q₃ = (K.a * K.h + K.c * K.f - K.b * K.g - K.d * K.e) ^ 2
      - 4 * (K.a * K.f - K.b * K.e) * (K.c * K.h - K.d * K.g) := by
  simp only [disc, Q₃]; ring

/-- **All three forms of a Bhargava cube have the same discriminant.** -/
theorem disc_Q₁_eq_disc_Q₂ : disc K.Q₁ = disc K.Q₂ := by
  rw [disc_Q₁, disc_Q₂]; ring

/-- **All three forms of a Bhargava cube have the same discriminant.** -/
theorem disc_Q₂_eq_disc_Q₃ : disc K.Q₂ = disc K.Q₃ := by
  rw [disc_Q₂, disc_Q₃]; ring

end Cube

/-- The common discriminant of the three forms attached to a Bhargava cube. -/
theorem cube_disc_eq (K : Cube) : disc K.Q₁ = disc K.Q₂ ∧ disc K.Q₂ = disc K.Q₃ :=
  ⟨K.disc_Q₁_eq_disc_Q₂, K.disc_Q₂_eq_disc_Q₃⟩

/-!
## The base case of the cube law

Fix integers `A, C, f, g` and put `B = g - f`. The cube

```
baseCube A C f g = (a,b,c,d,e,f,g,h) = (0, 1, 1, 0, A, f, g, -C)
```

has

* `Q₁ (x,y) = x² - (f+g) x y + (AC + fg) y²`, a form representing `1` (the *principal*
  form of its discriminant),
* `Q₂ (x,y) = A x² + B x y + C y²`, an arbitrary form of discriminant `B² - 4AC`,
* `Q₃ (x,y) = A x² - B x y + C y²`, the opposite (inverse) form.

All three have discriminant `B² - 4AC`. The cube law `[Q₁][Q₂][Q₃] = 1` therefore
specialises to Gauss's statement that a form composed with its opposite is principal,
and it is witnessed here by an explicit bilinear composition identity.
-/

/-- The base cube `(0, 1, 1, 0, A, f, g, -C)`. -/
def baseCube (A C f g : ℤ) : Cube := ⟨0, 1, 1, 0, A, f, g, -C⟩

@[simp] lemma baseCube_Q₁ (A C f g x y : ℤ) :
    (baseCube A C f g).Q₁ x y = x ^ 2 - (f + g) * x * y + (A * C + f * g) * y ^ 2 := by
  simp only [baseCube, Cube.Q₁]; ring

@[simp] lemma baseCube_Q₂ (A C f g x y : ℤ) :
    (baseCube A C f g).Q₂ x y = A * x ^ 2 + (g - f) * x * y + C * y ^ 2 := by
  simp only [baseCube, Cube.Q₂]; ring

@[simp] lemma baseCube_Q₃ (A C f g x y : ℤ) :
    (baseCube A C f g).Q₃ x y = A * x ^ 2 - (g - f) * x * y + C * y ^ 2 := by
  simp only [baseCube, Cube.Q₃]; ring

/-- The principal form `Q₁` of the base cube represents `1`. -/
lemma baseCube_Q₁_one (A C f g : ℤ) : (baseCube A C f g).Q₁ 1 0 = 1 := by
  simp

/-- The three forms of the base cube all have discriminant `(g - f)² - 4AC`. -/
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
theorem bhargava_cube_law (A C f g : ℤ) :
    (disc (baseCube A C f g).Q₁ = (g - f) ^ 2 - 4 * A * C ∧
      disc (baseCube A C f g).Q₂ = (g - f) ^ 2 - 4 * A * C ∧
      disc (baseCube A C f g).Q₃ = (g - f) ^ 2 - 4 * A * C) ∧
    (baseCube A C f g).Q₁ 1 0 = 1 ∧
    (∀ x y : ℤ, (baseCube A C f g).Q₂ x y = A * x ^ 2 + (g - f) * x * y + C * y ^ 2) ∧
    (∀ x y : ℤ, (baseCube A C f g).Q₃ x y = A * x ^ 2 - (g - f) * x * y + C * y ^ 2) ∧
    (∀ x₁ y₁ x₂ y₂ : ℤ,
      (baseCube A C f g).Q₂ x₁ y₁ * (baseCube A C f g).Q₃ x₂ y₂ =
        (baseCube A C f g).Q₁
          (A * x₁ * x₂ + f * x₁ * y₂ + g * x₂ * y₁ - C * y₁ * y₂)
          (x₁ * y₂ + x₂ * y₁)) := by
  refine ⟨baseCube_disc A C f g, baseCube_Q₁_one A C f g, fun x y => baseCube_Q₂ A C f g x y,
    fun x y => baseCube_Q₃ A C f g x y, fun x₁ y₁ x₂ y₂ => ?_⟩
  simp only [baseCube_Q₁, baseCube_Q₂, baseCube_Q₃]
  ring

/-!
## Consequences: Gauss composition of a form with its opposite
-/

/-- Gauss composition, even discriminant case: for `Q(x,y) = A x² + 2k x y + C y²`,
the product `Q(x₁,y₁) · Q̄(x₂,y₂)` is represented by the principal form
`X² - (k² - AC) Y²` of the same discriminant `4(k² - AC)`. -/
theorem gauss_compose_opposite_even (A C k x₁ y₁ x₂ y₂ : ℤ) :
    (A * x₁ ^ 2 + 2 * k * x₁ * y₁ + C * y₁ ^ 2) * (A * x₂ ^ 2 - 2 * k * x₂ * y₂ + C * y₂ ^ 2) =
      (A * x₁ * x₂ - k * x₁ * y₂ + k * x₂ * y₁ - C * y₁ * y₂) ^ 2
        - (k ^ 2 - A * C) * (x₁ * y₂ + x₂ * y₁) ^ 2 := by
  have := (bhargava_cube_law A C (-k) k).2.2.2.2 x₁ y₁ x₂ y₂
  simp only [baseCube_Q₁, baseCube_Q₂, baseCube_Q₃] at this
  linear_combination this

/-- Gauss composition, odd discriminant case: for `Q(x,y) = A x² + (2k+1) x y + C y²`,
the product `Q(x₁,y₁) · Q̄(x₂,y₂)` is represented by the principal form
`X² + X Y + (AC - k² - k) Y²` of the same discriminant `(2k+1)² - 4AC`. -/
theorem gauss_compose_opposite_odd (A C k x₁ y₁ x₂ y₂ : ℤ) :
    (A * x₁ ^ 2 + (2 * k + 1) * x₁ * y₁ + C * y₁ ^ 2) *
        (A * x₂ ^ 2 - (2 * k + 1) * x₂ * y₂ + C * y₂ ^ 2) =
      (A * x₁ * x₂ - (k + 1) * x₁ * y₂ + k * x₂ * y₁ - C * y₁ * y₂) ^ 2
        + (A * x₁ * x₂ - (k + 1) * x₁ * y₂ + k * x₂ * y₁ - C * y₁ * y₂) * (x₁ * y₂ + x₂ * y₁)
        + (A * C - k ^ 2 - k) * (x₁ * y₂ + x₂ * y₁) ^ 2 := by
  have := (bhargava_cube_law A C (-(k + 1)) k).2.2.2.2 x₁ y₁ x₂ y₂
  simp only [baseCube_Q₁, baseCube_Q₂, baseCube_Q₃] at this
  linear_combination this

end Frontier


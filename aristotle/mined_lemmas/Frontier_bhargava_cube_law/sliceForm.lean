/-
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
## Bhargava cubes and their three pairs of `2 × 2` slices

A *Bhargava cube* is an element of `ℤ² ⊗ ℤ² ⊗ ℤ²`, i.e. an eight-tuple of integers
`(a, b, c, d, e, f, g, h)` placed at the vertices of a cube:

```
        e ------- f
       /|        /|
      a ------- b |
      | g ------|-h
      |/        |/
      c ------- d
```

Cutting the cube by planes orthogonal to each of the three coordinate directions produces
three pairs of `2 × 2` integer matrices

* `(M₁, N₁) = ((a b; c d), (e f; g h))`  (front/back),
* `(M₂, N₂) = ((a c; e g), (b d; f h))`  (left/right),
* `(M₃, N₃) = ((a e; b f), (c g; d h))`  (top/bottom),

and each pair yields the binary quadratic form `Qᵢ(x, y) = -det(Mᵢ x - Nᵢ y)`.
-/

/-- The binary quadratic form `Q (x, y) = -det (M x - N y)` attached to a pair of `2 × 2`
integer matrices `M = (m₁₁ m₁₂; m₂₁ m₂₂)` and `N = (n₁₁ n₁₂; n₂₁ n₂₂)`. -/

def sliceForm (m₁₁ m₁₂ m₂₁ m₂₂ n₁₁ n₁₂ n₂₁ n₂₂ x y : ℤ) : ℤ :=
  -((m₁₁ * x - n₁₁ * y) * (m₂₂ * x - n₂₂ * y) - (m₁₂ * x - n₁₂ * y) * (m₂₁ * x - n₂₁ * y))

/-- The first quadratic form `Q₁` of the Bhargava cube `(a, b, c, d, e, f, g, h)`,
coming from the front/back slicing `(M₁, N₁) = ((a b; c d), (e f; g h))`. -/

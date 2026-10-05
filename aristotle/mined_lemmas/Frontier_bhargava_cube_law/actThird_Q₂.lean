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

/-- An integral binary quadratic form `A x ^ 2 + B x y + C y ^ 2`, recorded by its
coefficient triple `(A, B, C)`. -/
structure BQF where
  A : ℤ
  B : ℤ
  C : ℤ
deriving DecidableEq

namespace BQF

/-- The discriminant `B ^ 2 - 4 A C` of a binary quadratic form. -/

lemma actThird_Q₂ (K : Cube) {p q r s : ℤ} (hdet : p * s - q * r = 1) :
    (K.actThird p q r s).Q₂ = K.Q₂ := by
  simp only [actThird, Q₂, BQF.mk.injEq]
  refine ⟨by linear_combination (K.c * K.e - K.a * K.g) * hdet,
    by linear_combination (K.c * K.f + K.d * K.e - K.a * K.h - K.b * K.g) * hdet,
    by linear_combination (K.d * K.f - K.b * K.h) * hdet⟩

end Cube

/-! ### The cube law -/

/--
**Bhargava's cube law** (base cases).

For a Bhargava cube `K` (an element of `ℤ² ⊗ ℤ² ⊗ ℤ²`) the three ways of slicing the cube
into a pair of `2 × 2` matrices `(Mᵢ, Nᵢ)` produce three binary quadratic forms
`Qᵢ(x, y) = -det (x Mᵢ + y Nᵢ)`.  The statement below records:

1. the three forms of a cube are indeed the negated determinants of the three slice pencils;
2. the three forms all have the same discriminant, namely the discriminant of the cube
   (so they lie in the same form class group);
3. *identity/base case*: every form `q` occurs in a cube together with the principal form of
   the same discriminant and the opposite form `q̄`, i.e. the cube law
   `[Q₁] [Q₂] [Q₃] = 1` specialises to `[q] [q̄] = 1` with `[Q₁]` the identity class;
4. *Gauss composition*: Dirichlet's composition of the concordant forms `(a₁, b, a₂ c)` and
   `(a₂, b, a₁ c)`, whose composite is `(a₁ a₂, b, c)`, is realised by an explicit cube:
   the three forms of that cube are `(a₁, b, a₂ c)`, `(a₂, b, a₁ c)` and the opposite of
   `(a₁ a₂, b, c)`, exactly as the relation `[Q₁] [Q₂] [Q₃] = 1` demands;
5. *covariance*: for `γ = !![p, q; r, s]` in `SL₂(ℤ)` acting on the `i`-th tensor factor of the
   cube, the form `Qᵢ` is replaced by its substitution `Qᵢ ∘ γ` — a properly equivalent form —
   while the other two forms are left unchanged.  Hence the triple of form classes
   `([Q₁], [Q₂], [Q₃])` depends only on the `SL₂(ℤ)³`-orbit of the cube.
-/

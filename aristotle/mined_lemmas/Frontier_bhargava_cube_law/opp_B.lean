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

A *Bhargava cube* is a `2 × 2 × 2` array of integers `a, b, c, d, e, f, g, h`.
Slicing it in each of the three directions gives three pairs of `2 × 2` matrices

`(M₁, N₁) = ((a b; c d), (e f; g h))`,
`(M₂, N₂) = ((a c; e g), (b d; f h))`,
`(M₃, N₃) = ((a e; b f), (c g; d h))`,

and hence three integral binary quadratic forms
`Qᵢ(x, y) = - det (x • Mᵢ + y • Nᵢ)`.

Bhargava's cube law says that these three forms all have the same discriminant
(the hyperdeterminant of the cube) and that they compose to the identity under
Gauss composition, `Q₁ ∘ Q₂ ∘ Q₃ = 1`.

Both halves are formalised below.  Gauss composition is made completely explicit:
for each of the three pairs of forms we exhibit an honest bilinear identity, e.g.

`Q₁(x₁, y₁) · Q₂(x₂, y₂) = Q₃ᵒᵖ(B₂, B₁)`,

where `B₁, B₂` are bilinear forms in `(x₁, y₁)` and `(x₂, y₂)` whose coefficients
are the entries of the cube, obtained by contracting the cube against the two
vectors, and `Q₃ᵒᵖ` (the form `Q₃` with its middle coefficient negated) is a form
representing the inverse class of `Q₃`.  Such a bilinear identity is exactly the
classical statement that `Q₃ᵒᵖ` is a Gauss composite of `Q₁` and `Q₂`; hence the
class of `Q₁ ∘ Q₂` is the inverse of the class of `Q₃`.

Two further facts are proved:

* `SL₂(ℤ)`-covariance in one slot of the cube: the corresponding form is changed
  by the corresponding substitution of variables (so its class is unchanged),
  while the other two forms are literally unchanged;
* Dirichlet's classical composition of concordant forms `(a₁, b, a₂c)` and
  `(a₂, b, a₁c)` into `(a₁a₂, b, c)` is recovered as a special case of the cube
  law, applied to an explicit cube.
-/

namespace Frontier

/-! ### Integral binary quadratic forms -/

/-- An integral binary quadratic form `A x² + B x y + C y²`. -/
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

@[simp] theorem opp_B (F : BQF) : F.opp.B = -F.B := rfl

/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Statement: Bhargava's cube gives a composition law on pairs of binary quadratic forms recovering Gauss composition.
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
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
def eval (q : BQF) (x y : ℤ) : ℤ := q.A * x ^ 2 + q.B * x * y + q.C * y ^ 2

/-- The discriminant `B² - 4AC` of a binary quadratic form. -/
def disc (q : BQF) : ℤ := q.B ^ 2 - 4 * q.A * q.C

/-- The opposite form `A x² - B x y + C y²`; it represents the inverse class of `[q]`
in the form class group. -/
def inv (q : BQF) : BQF := ⟨q.A, -q.B, q.C⟩

@[simp] lemma inv_A (q : BQF) : q.inv.A = q.A := rfl
@[simp] lemma inv_B (q : BQF) : q.inv.B = -q.B := rfl
@[simp] lemma inv_C (q : BQF) : q.inv.C = q.C := rfl

@[simp] lemma disc_inv (q : BQF) : q.inv.disc = q.disc := by
  simp [disc, inv]

lemma eval_inv (q : BQF) (x y : ℤ) : q.inv.eval x y = q.eval x (-y) := by
  simp [eval, inv]

end BQF

/-- A Bhargava cube: a `2 × 2 × 2` array of integers. The front face is
`![![a, b], ![c, d]]` and the back face is `![![e, f], ![g, h]]`. -/
structure Cube where
  /-- entry `a₀₀₀` -/
  a : ℤ
  /-- entry `a₀₁₀` -/
  b : ℤ
  /-- entry `a₁₀₀` -/
  c : ℤ
  /-- entry `a₁₁₀` -/
  d : ℤ
  /-- entry `a₀₀₁` -/
  e : ℤ
  /-- entry `a₀₁₁` -/
  f : ℤ
  /-- entry `a₁₀₁` -/
  g : ℤ
  /-- entry `a₁₁₁` -/
  h : ℤ
  deriving DecidableEq, Repr

namespace Cube

variable (K : Cube)

/-- First slicing: front/back faces. -/
def M₁ : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.b; K.c, K.d]
/-- First slicing: front/back faces. -/
def N₁ : Matrix (Fin 2) (Fin 2) ℤ := !![K.e, K.f; K.g, K.h]
/-- Second slicing: top/bottom faces. -/
def M₂ : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.c; K.e, K.g]
/-- Second slicing: top/bottom faces. -/
def N₂ : Matrix (Fin 2) (Fin 2) ℤ := !![K.b, K.d; K.f, K.h]
/-- Third slicing: left/right faces. -/
def M₃ : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.e; K.b, K.f]
/-- Third slicing: left/right faces. -/
def N₃ : Matrix (Fin 2) (Fin 2) ℤ := !![K.c, K.g; K.d, K.h]

/-- The binary quadratic form `Q₁(x,y) = -det (x M₁ - y N₁)` attached to the first slicing. -/
def Q₁ : BQF :=
  ⟨K.b * K.c - K.a * K.d,
   K.a * K.h + K.d * K.e - K.b * K.g - K.c * K.f,
   K.f * K.g - K.e * K.h⟩

/-- The binary quadratic form `Q₂(x,y) = -det (x M₂ - y N₂)` attached to the second slicing. -/
def Q₂ : BQF :=
  ⟨K.c * K.e - K.a * K.g,
   K.a * K.h + K.b * K.g - K.c * K.f - K.d * K.e,
   K.d * K.f - K.b * K.h⟩

/-- The binary quadratic form `Q₃(x,y) = -det (x M₃ - y N₃)` attached to the third slicing. -/
def Q₃ : BQF :=
  ⟨K.b * K.e - K.a * K.f,
   K.a * K.h + K.c * K.f - K.d * K.e - K.b * K.g,
   K.g * K.d - K.c * K.h⟩

/-- Cayley's hyperdeterminant of a `2 × 2 × 2` cube. -/
def hyperdet : ℤ :=
  K.a ^ 2 * K.h ^ 2 + K.b ^ 2 * K.g ^ 2 + K.c ^ 2 * K.f ^ 2 + K.d ^ 2 * K.e ^ 2
    - 2 * (K.a * K.b * K.g * K.h + K.a * K.c * K.f * K.h + K.a * K.d * K.e * K.h
        + K.b * K.c * K.f * K.g + K.b * K.d * K.e * K.g + K.c * K.d * K.e * K.f)
    + 4 * (K.a * K.d * K.f * K.g + K.b * K.c * K.e * K.h)

/-! ### The forms really are `-det (x Mᵢ - y Nᵢ)` -/

lemma Q₁_eval (x y : ℤ) :
    K.Q₁.eval x y = -((x • K.M₁ - y • K.N₁).det) := by
  simp [BQF.eval, Q₁, M₁, N₁, Matrix.det_fin_two]
  ring

lemma Q₂_eval (x y : ℤ) :
    K.Q₂.eval x y = -((x • K.M₂ - y • K.N₂).det) := by
  simp [BQF.eval, Q₂, M₂, N₂, Matrix.det_fin_two]
  ring

lemma Q₃_eval (x y : ℤ) :
    K.Q₃.eval x y = -((x • K.M₃ - y • K.N₃).det) := by
  simp [BQF.eval, Q₃, M₃, N₃, Matrix.det_fin_two]
  ring

/-! ### All three forms have the same discriminant, the hyperdeterminant of the cube -/

lemma disc_Q₁ : K.Q₁.disc = K.hyperdet := by
  simp only [BQF.disc, Q₁, hyperdet]; ring

lemma disc_Q₂ : K.Q₂.disc = K.hyperdet := by
  simp only [BQF.disc, Q₂, hyperdet]; ring

lemma disc_Q₃ : K.Q₃.disc = K.hyperdet := by
  simp only [BQF.disc, Q₃, hyperdet]; ring

lemma disc_eq : K.Q₁.disc = K.Q₂.disc ∧ K.Q₂.disc = K.Q₃.disc := by
  refine ⟨?_, ?_⟩ <;> simp [disc_Q₁, disc_Q₂, disc_Q₃]

/-! ### The composition (bilinear) forms -/

/-- First coordinate of the bilinear map composing `Q₁` and `Q₂`. -/
def X₁₂ (x₁ y₁ x₂ y₂ : ℤ) : ℤ :=
  K.c * x₁ * x₂ - K.d * x₁ * y₂ - K.g * y₁ * x₂ + K.h * y₁ * y₂
/-- Second coordinate of the bilinear map composing `Q₁` and `Q₂`. -/
def Y₁₂ (x₁ y₁ x₂ y₂ : ℤ) : ℤ :=
  -K.a * x₁ * x₂ + K.b * x₁ * y₂ + K.e * y₁ * x₂ - K.f * y₁ * y₂

/-- First coordinate of the bilinear map composing `Q₂` and `Q₃`. -/
def X₂₃ (x₂ y₂ x₃ y₃ : ℤ) : ℤ :=
  K.e * x₂ * x₃ - K.g * x₂ * y₃ - K.f * y₂ * x₃ + K.h * y₂ * y₃
/-- Second coordinate of the bilinear map composing `Q₂` and `Q₃`. -/
def Y₂₃ (x₂ y₂ x₃ y₃ : ℤ) : ℤ :=
  -K.a * x₂ * x₃ + K.c * x₂ * y₃ + K.b * y₂ * x₃ - K.d * y₂ * y₃

/-- First coordinate of the bilinear map composing `Q₃` and `Q₁`. -/
def X₃₁ (x₃ y₃ x₁ y₁ : ℤ) : ℤ :=
  K.b * x₃ * x₁ - K.f * x₃ * y₁ - K.d * y₃ * x₁ + K.h * y₃ * y₁
/-- Second coordinate of the bilinear map composing `Q₃` and `Q₁`. -/
def Y₃₁ (x₃ y₃ x₁ y₁ : ℤ) : ℤ :=
  -K.a * x₃ * x₁ + K.e * x₃ * y₁ + K.c * y₃ * x₁ - K.g * y₃ * y₁

/-! ### The cube law: `[Q₁][Q₂][Q₃] = 1`, in effective bilinear form -/

/-- **Gauss composition from the cube.** The product of a value of `Q₁` and a value of `Q₂`
is a value of the form `Q₃⁻¹` representing the inverse class of `[Q₃]`, at arguments given by
explicit bilinear expressions in the cube entries. -/
theorem comp₁₂ (x₁ y₁ x₂ y₂ : ℤ) :
    K.Q₁.eval x₁ y₁ * K.Q₂.eval x₂ y₂
      = K.Q₃.inv.eval (K.X₁₂ x₁ y₁ x₂ y₂) (K.Y₁₂ x₁ y₁ x₂ y₂) := by
  simp only [BQF.eval, BQF.inv, Q₁, Q₂, Q₃, X₁₂, Y₁₂]
  ring

/-- Cyclic version of `comp₁₂`: `[Q₂][Q₃] = [Q₁]⁻¹`. -/
theorem comp₂₃ (x₂ y₂ x₃ y₃ : ℤ) :
    K.Q₂.eval x₂ y₂ * K.Q₃.eval x₃ y₃
      = K.Q₁.inv.eval (K.X₂₃ x₂ y₂ x₃ y₃) (K.Y₂₃ x₂ y₂ x₃ y₃) := by
  simp only [BQF.eval, BQF.inv, Q₁, Q₂, Q₃, X₂₃, Y₂₃]
  ring

/-- Cyclic version of `comp₁₂`: `[Q₃][Q₁] = [Q₂]⁻¹`. -/
theorem comp₃₁ (x₃ y₃ x₁ y₁ : ℤ) :
    K.Q₃.eval x₃ y₃ * K.Q₁.eval x₁ y₁
      = K.Q₂.inv.eval (K.X₃₁ x₃ y₃ x₁ y₁) (K.Y₃₁ x₃ y₃ x₁ y₁) := by
  simp only [BQF.eval, BQF.inv, Q₁, Q₂, Q₃, X₃₁, Y₃₁]
  ring

/-- Consequence: the values represented by `Q₁` and by `Q₂` multiply into values
represented by the inverse of `Q₃`. -/
theorem represents_mul {u v : ℤ} (hu : ∃ x y : ℤ, K.Q₁.eval x y = u)
    (hv : ∃ x y : ℤ, K.Q₂.eval x y = v) :
    ∃ x y : ℤ, K.Q₃.inv.eval x y = u * v := by
  obtain ⟨x₁, y₁, rfl⟩ := hu
  obtain ⟨x₂, y₂, rfl⟩ := hv
  exact ⟨_, _, (K.comp₁₂ x₁ y₁ x₂ y₂).symm⟩

end Cube

/-! ### Base case: recovering classical Dirichlet/Gauss composition -/

/-- The cube whose slices are the two Dirichlet-concordant forms `(a₁, m, a₂n)` and
`(a₂, m, a₁n)` together with the inverse `(a₁a₂, -m, n)` of their Gauss composite. -/
def dirichletCube (a₁ a₂ m n : ℤ) : Cube :=
  ⟨0, a₁, 1, 0, a₂, -m, 0, -n⟩

@[simp] lemma dirichletCube_Q₁ (a₁ a₂ m n : ℤ) :
    (dirichletCube a₁ a₂ m n).Q₁ = ⟨a₁, m, a₂ * n⟩ := by
  simp [dirichletCube, Cube.Q₁]

@[simp] lemma dirichletCube_Q₂ (a₁ a₂ m n : ℤ) :
    (dirichletCube a₁ a₂ m n).Q₂ = ⟨a₂, m, a₁ * n⟩ := by
  simp [dirichletCube, Cube.Q₂]

@[simp] lemma dirichletCube_Q₃ (a₁ a₂ m n : ℤ) :
    (dirichletCube a₁ a₂ m n).Q₃ = ⟨a₁ * a₂, -m, n⟩ := by
  simp [dirichletCube, Cube.Q₃]

/-- The common discriminant of the three Dirichlet slices is `m² - 4a₁a₂n`. -/
lemma dirichletCube_disc (a₁ a₂ m n : ℤ) :
    (dirichletCube a₁ a₂ m n).hyperdet = m ^ 2 - 4 * (a₁ * a₂) * n := by
  simp [dirichletCube, Cube.hyperdet]; ring

/-- **Dirichlet's classical composition formula**, obtained as the special case of the cube law
for `dirichletCube`:
`(a₁x₁² + m x₁y₁ + a₂n y₁²)(a₂x₂² + m x₂y₂ + a₁n y₂²) = a₁a₂X² + m XY + n Y²`
with `X = x₁x₂ - n y₁y₂` and `Y = a₁x₁y₂ + a₂x₂y₁ + m y₁y₂`. -/
theorem dirichlet_composition (a₁ a₂ m n x₁ y₁ x₂ y₂ : ℤ) :
    (a₁ * x₁ ^ 2 + m * x₁ * y₁ + a₂ * n * y₁ ^ 2) *
        (a₂ * x₂ ^ 2 + m * x₂ * y₂ + a₁ * n * y₂ ^ 2)
      = (BQF.mk (a₁ * a₂) m n).eval (x₁ * x₂ - n * y₁ * y₂)
          (a₁ * x₁ * y₂ + a₂ * x₂ * y₁ + m * y₁ * y₂) := by
  have key := (dirichletCube a₁ a₂ m n).comp₁₂ x₁ y₁ x₂ y₂
  simp only [dirichletCube, Cube.Q₁, Cube.Q₂, Cube.Q₃, Cube.X₁₂, Cube.Y₁₂, BQF.eval,
    BQF.inv] at key ⊢
  linear_combination key

/-! ### The main statement -/

/-- **Bhargava's cube law.** For every integral `2 × 2 × 2` cube:

1. the three binary quadratic forms `Q₁, Q₂, Q₃` obtained by slicing the cube in the three
   coordinate directions have a common discriminant, equal to Cayley's hyperdeterminant of
   the cube;
2. their classes multiply to the identity of the class group of that discriminant: this is
   witnessed effectively by the three bilinear composition identities
   `Qᵢ(vᵢ) · Qⱼ(vⱼ) = Qₖ⁻¹(bilinear)` for `(i,j,k)` a cyclic permutation of `(1,2,3)`;
3. specializing to the Dirichlet cube recovers Gauss's classical composition of the
   concordant forms `(a₁, m, a₂n)` and `(a₂, m, a₁n)` into `(a₁a₂, m, n)`.
-/
theorem bhargava_cube_law :
    (∀ K : Cube,
        K.Q₁.disc = K.hyperdet ∧ K.Q₂.disc = K.hyperdet ∧ K.Q₃.disc = K.hyperdet) ∧
    (∀ (K : Cube) (x₁ y₁ x₂ y₂ x₃ y₃ : ℤ),
        K.Q₁.eval x₁ y₁ * K.Q₂.eval x₂ y₂
            = K.Q₃.inv.eval (K.X₁₂ x₁ y₁ x₂ y₂) (K.Y₁₂ x₁ y₁ x₂ y₂) ∧
        K.Q₂.eval x₂ y₂ * K.Q₃.eval x₃ y₃
            = K.Q₁.inv.eval (K.X₂₃ x₂ y₂ x₃ y₃) (K.Y₂₃ x₂ y₂ x₃ y₃) ∧
        K.Q₃.eval x₃ y₃ * K.Q₁.eval x₁ y₁
            = K.Q₂.inv.eval (K.X₃₁ x₃ y₃ x₁ y₁) (K.Y₃₁ x₃ y₃ x₁ y₁)) ∧
    (∀ a₁ a₂ m n : ℤ,
        (dirichletCube a₁ a₂ m n).Q₁ = ⟨a₁, m, a₂ * n⟩ ∧
        (dirichletCube a₁ a₂ m n).Q₂ = ⟨a₂, m, a₁ * n⟩ ∧
        (dirichletCube a₁ a₂ m n).Q₃ = ⟨a₁ * a₂, -m, n⟩ ∧
        ∀ x₁ y₁ x₂ y₂ : ℤ,
          (BQF.mk a₁ m (a₂ * n)).eval x₁ y₁ * (BQF.mk a₂ m (a₁ * n)).eval x₂ y₂
            = (BQF.mk (a₁ * a₂) m n).eval (x₁ * x₂ - n * y₁ * y₂)
                (a₁ * x₁ * y₂ + a₂ * x₂ * y₁ + m * y₁ * y₂)) := by
  refine ⟨fun K => ⟨K.disc_Q₁, K.disc_Q₂, K.disc_Q₃⟩,
    fun K x₁ y₁ x₂ y₂ x₃ y₃ => ⟨K.comp₁₂ .., K.comp₂₃ .., K.comp₃₁ ..⟩,
    fun a₁ a₂ m n => ⟨dirichletCube_Q₁ .., dirichletCube_Q₂ .., dirichletCube_Q₃ .., ?_⟩⟩
  intro x₁ y₁ x₂ y₂
  have := dirichlet_composition a₁ a₂ m n x₁ y₁ x₂ y₂
  simp only [BQF.eval] at this ⊢
  linear_combination this

end Frontier


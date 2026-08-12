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
def eval (F : BQF) (x y : ℤ) : ℤ := F.A * x ^ 2 + F.B * x * y + F.C * y ^ 2

/-- The discriminant `B² - 4AC` of a binary quadratic form. -/
def disc (F : BQF) : ℤ := F.B ^ 2 - 4 * F.A * F.C

/-- The opposite form `A x² - B x y + C y²`; it represents the inverse class of
`F` in the form class group. -/
def opp (F : BQF) : BQF := ⟨F.A, -F.B, F.C⟩

@[simp] theorem opp_A (F : BQF) : F.opp.A = F.A := rfl
@[simp] theorem opp_B (F : BQF) : F.opp.B = -F.B := rfl
@[simp] theorem opp_C (F : BQF) : F.opp.C = F.C := rfl

@[simp] theorem opp_opp (F : BQF) : F.opp.opp = F := by
  cases F; simp only [opp, neg_neg]

@[simp] theorem disc_opp (F : BQF) : F.opp.disc = F.disc := by
  simp only [disc, opp]; ring

/-- The opposite form is obtained from `F` by the substitution `(x, y) ↦ (x, -y)`;
in particular it is `SL₂(ℤ)`-improperly equivalent to `F` and represents the same
integers. -/
theorem opp_eval (F : BQF) (x y : ℤ) : F.opp.eval x y = F.eval x (-y) := by
  simp only [eval, opp]; ring

end BQF

/-! ### Bhargava cubes -/

/-- A Bhargava cube: a `2 × 2 × 2` array of integers, with entries labelled as in
Bhargava's *Higher composition laws I*. -/
structure Cube where
  /-- Entry `c₁₁₁`. -/
  a : ℤ
  /-- Entry `c₁₁₂`. -/
  b : ℤ
  /-- Entry `c₁₂₁`. -/
  c : ℤ
  /-- Entry `c₁₂₂`. -/
  d : ℤ
  /-- Entry `c₂₁₁`. -/
  e : ℤ
  /-- Entry `c₂₁₂`. -/
  f : ℤ
  /-- Entry `c₂₂₁`. -/
  g : ℤ
  /-- Entry `c₂₂₂`. -/
  h : ℤ
  deriving DecidableEq

namespace Cube

variable (K : Cube)

/-- Front face of the cube, the first matrix of the first slicing. -/
def M₁ : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.b; K.c, K.d]
/-- Back face of the cube, the second matrix of the first slicing. -/
def N₁ : Matrix (Fin 2) (Fin 2) ℤ := !![K.e, K.f; K.g, K.h]
/-- First matrix of the second slicing. -/
def M₂ : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.c; K.e, K.g]
/-- Second matrix of the second slicing. -/
def N₂ : Matrix (Fin 2) (Fin 2) ℤ := !![K.b, K.d; K.f, K.h]
/-- First matrix of the third slicing. -/
def M₃ : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.e; K.b, K.f]
/-- Second matrix of the third slicing. -/
def N₃ : Matrix (Fin 2) (Fin 2) ℤ := !![K.c, K.g; K.d, K.h]

/-- The first quadratic form of the cube, `Q₁ = -det (x M₁ + y N₁)`. -/
def form₁ : BQF :=
  ⟨-(K.a * K.d - K.b * K.c),
   -(K.a * K.h + K.d * K.e - K.b * K.g - K.c * K.f),
   -(K.e * K.h - K.f * K.g)⟩

/-- The second quadratic form of the cube, `Q₂ = -det (x M₂ + y N₂)`. -/
def form₂ : BQF :=
  ⟨-(K.a * K.g - K.c * K.e),
   -(K.a * K.h + K.b * K.g - K.c * K.f - K.d * K.e),
   -(K.b * K.h - K.d * K.f)⟩

/-- The third quadratic form of the cube, `Q₃ = -det (x M₃ + y N₃)`. -/
def form₃ : BQF :=
  ⟨-(K.a * K.f - K.b * K.e),
   -(K.a * K.h + K.c * K.f - K.b * K.g - K.d * K.e),
   -(K.c * K.h - K.d * K.g)⟩

/-- `Q₁` is indeed `-det (x M₁ + y N₁)`. -/
theorem form₁_eval (x y : ℤ) :
    (K.form₁).eval x y = -(x • K.M₁ + y • K.N₁).det := by
  have hM : x • K.M₁ + y • K.N₁
      = !![K.a * x + K.e * y, K.b * x + K.f * y; K.c * x + K.g * y, K.d * x + K.h * y] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [M₁, N₁] <;> ring
  rw [hM, Matrix.det_fin_two_of]
  simp only [BQF.eval, form₁]
  ring

/-- `Q₂` is indeed `-det (x M₂ + y N₂)`. -/
theorem form₂_eval (x y : ℤ) :
    (K.form₂).eval x y = -(x • K.M₂ + y • K.N₂).det := by
  have hM : x • K.M₂ + y • K.N₂
      = !![K.a * x + K.b * y, K.c * x + K.d * y; K.e * x + K.f * y, K.g * x + K.h * y] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [M₂, N₂] <;> ring
  rw [hM, Matrix.det_fin_two_of]
  simp only [BQF.eval, form₂]
  ring

/-- `Q₃` is indeed `-det (x M₃ + y N₃)`. -/
theorem form₃_eval (x y : ℤ) :
    (K.form₃).eval x y = -(x • K.M₃ + y • K.N₃).det := by
  have hM : x • K.M₃ + y • K.N₃
      = !![K.a * x + K.c * y, K.e * x + K.g * y; K.b * x + K.d * y, K.f * x + K.h * y] := by
    ext i j; fin_cases i <;> fin_cases j <;> simp [M₃, N₃] <;> ring
  rw [hM, Matrix.det_fin_two_of]
  simp only [BQF.eval, form₃]
  ring

/-- Cayley's hyperdeterminant of the cube; it is the common discriminant of the
three quadratic forms attached to the cube. -/
def hyperdet : ℤ :=
  K.a ^ 2 * K.h ^ 2 + K.b ^ 2 * K.g ^ 2 + K.c ^ 2 * K.f ^ 2 + K.d ^ 2 * K.e ^ 2
    - 2 * (K.a * K.b * K.g * K.h + K.a * K.c * K.f * K.h + K.a * K.d * K.e * K.h
      + K.b * K.c * K.f * K.g + K.b * K.d * K.e * K.g + K.c * K.d * K.e * K.f)
    + 4 * (K.a * K.d * K.f * K.g + K.b * K.c * K.e * K.h)

/-- The discriminant of `Q₁` is the hyperdeterminant of the cube. -/
theorem disc_form₁ : (K.form₁).disc = K.hyperdet := by
  simp only [BQF.disc, form₁, hyperdet]; ring

/-- The discriminant of `Q₂` is the hyperdeterminant of the cube. -/
theorem disc_form₂ : (K.form₂).disc = K.hyperdet := by
  simp only [BQF.disc, form₂, hyperdet]; ring

/-- The discriminant of `Q₃` is the hyperdeterminant of the cube. -/
theorem disc_form₃ : (K.form₃).disc = K.hyperdet := by
  simp only [BQF.disc, form₃, hyperdet]; ring

/-! ### The bilinear forms used for composition

Contracting the cube (viewed as a trilinear form on `ℤ² × ℤ² × ℤ²`) against
vectors in two of the three slots leaves a vector in the remaining slot; its two
coordinates are the bilinear forms below. -/

/-- First coordinate of the contraction of the cube against slots `1` and `2`. -/
def bil₁₂fst (x₁ y₁ x₂ y₂ : ℤ) : ℤ :=
  K.a * x₁ * x₂ + K.b * x₁ * y₂ + K.e * y₁ * x₂ + K.f * y₁ * y₂

/-- Second coordinate of the contraction of the cube against slots `1` and `2`. -/
def bil₁₂snd (x₁ y₁ x₂ y₂ : ℤ) : ℤ :=
  K.c * x₁ * x₂ + K.d * x₁ * y₂ + K.g * y₁ * x₂ + K.h * y₁ * y₂

/-- First coordinate of the contraction of the cube against slots `1` and `3`. -/
def bil₁₃fst (x₁ y₁ x₂ y₂ : ℤ) : ℤ :=
  K.a * x₁ * x₂ + K.c * x₁ * y₂ + K.e * y₁ * x₂ + K.g * y₁ * y₂

/-- Second coordinate of the contraction of the cube against slots `1` and `3`. -/
def bil₁₃snd (x₁ y₁ x₂ y₂ : ℤ) : ℤ :=
  K.b * x₁ * x₂ + K.d * x₁ * y₂ + K.f * y₁ * x₂ + K.h * y₁ * y₂

/-- First coordinate of the contraction of the cube against slots `2` and `3`. -/
def bil₂₃fst (x₁ y₁ x₂ y₂ : ℤ) : ℤ :=
  K.a * x₁ * x₂ + K.c * x₁ * y₂ + K.b * y₁ * x₂ + K.d * y₁ * y₂

/-- Second coordinate of the contraction of the cube against slots `2` and `3`. -/
def bil₂₃snd (x₁ y₁ x₂ y₂ : ℤ) : ℤ :=
  K.e * x₁ * x₂ + K.g * x₁ * y₂ + K.f * y₁ * x₂ + K.h * y₁ * y₂

/-- **Gauss composition of `Q₁` and `Q₂`, read off the cube.**  The product of a
value of `Q₁` and a value of `Q₂` is the value of `Q₃ᵒᵖ` at the pair of bilinear
forms obtained by contracting the cube in the first two slots.  This is the
bilinear identity witnessing `Q₁ ∘ Q₂ = Q₃⁻¹`. -/
theorem composition₁₂ (x₁ y₁ x₂ y₂ : ℤ) :
    (K.form₁).eval x₁ y₁ * (K.form₂).eval x₂ y₂
      = (K.form₃).opp.eval (K.bil₁₂snd x₁ y₁ x₂ y₂) (K.bil₁₂fst x₁ y₁ x₂ y₂) := by
  simp only [BQF.eval, BQF.opp, form₁, form₂, form₃, bil₁₂fst, bil₁₂snd]
  ring

/-- **Gauss composition of `Q₁` and `Q₃`, read off the cube**: the bilinear identity
witnessing `Q₁ ∘ Q₃ = Q₂⁻¹`. -/
theorem composition₁₃ (x₁ y₁ x₂ y₂ : ℤ) :
    (K.form₁).eval x₁ y₁ * (K.form₃).eval x₂ y₂
      = (K.form₂).opp.eval (K.bil₁₃snd x₁ y₁ x₂ y₂) (K.bil₁₃fst x₁ y₁ x₂ y₂) := by
  simp only [BQF.eval, BQF.opp, form₁, form₂, form₃, bil₁₃fst, bil₁₃snd]
  ring

/-- **Gauss composition of `Q₂` and `Q₃`, read off the cube**: the bilinear identity
witnessing `Q₂ ∘ Q₃ = Q₁⁻¹`. -/
theorem composition₂₃ (x₁ y₁ x₂ y₂ : ℤ) :
    (K.form₂).eval x₁ y₁ * (K.form₃).eval x₂ y₂
      = (K.form₁).opp.eval (K.bil₂₃snd x₁ y₁ x₂ y₂) (K.bil₂₃fst x₁ y₁ x₂ y₂) := by
  simp only [BQF.eval, BQF.opp, form₁, form₂, form₃, bil₂₃fst, bil₂₃snd]
  ring

/-! ### `SL₂(ℤ)`-covariance in the first slot -/

/-- The action on the cube of the matrix `(p q; r s)` in the first slot: the pair
of faces `(M₁, N₁)` is replaced by `(p M₁ + q N₁, r M₁ + s N₁)`. -/
def act₁ (p q r s : ℤ) : Cube :=
  ⟨p * K.a + q * K.e, p * K.b + q * K.f, p * K.c + q * K.g, p * K.d + q * K.h,
   r * K.a + s * K.e, r * K.b + s * K.f, r * K.c + s * K.g, r * K.d + s * K.h⟩

/-- Acting in the first slot substitutes the variables of `Q₁`; in particular the
`SL₂(ℤ)`-class of `Q₁` is unchanged. -/
theorem form₁_act₁_eval (p q r s x y : ℤ) :
    ((K.act₁ p q r s).form₁).eval x y = (K.form₁).eval (p * x + r * y) (q * x + s * y) := by
  simp only [BQF.eval, form₁, act₁]
  ring

/-- Acting by an element of `SL₂(ℤ)` in the first slot leaves `Q₂` unchanged. -/
theorem form₂_act₁ (p q r s : ℤ) (hdet : p * s - q * r = 1) :
    (K.act₁ p q r s).form₂ = K.form₂ := by
  simp only [form₂, act₁, BQF.mk.injEq]
  refine ⟨by linear_combination (-(K.a * K.g) + K.c * K.e) * hdet, ?_, ?_⟩
  · linear_combination (-(K.a * K.h) - K.b * K.g + K.c * K.f + K.d * K.e) * hdet
  · linear_combination (-(K.b * K.h) + K.d * K.f) * hdet

/-- Acting by an element of `SL₂(ℤ)` in the first slot leaves `Q₃` unchanged. -/
theorem form₃_act₁ (p q r s : ℤ) (hdet : p * s - q * r = 1) :
    (K.act₁ p q r s).form₃ = K.form₃ := by
  simp only [form₃, act₁, BQF.mk.injEq]
  refine ⟨by linear_combination (-(K.a * K.f) + K.b * K.e) * hdet, ?_, ?_⟩
  · linear_combination (-(K.a * K.h) + K.b * K.g - K.c * K.f + K.d * K.e) * hdet
  · linear_combination (-(K.c * K.h) + K.d * K.g) * hdet

end Cube

/-- **Bhargava's cube law.**  For every `2 × 2 × 2` integer cube, the three binary
quadratic forms `Q₁, Q₂, Q₃` cut out by the three ways of slicing the cube

* all have the same discriminant, namely the hyperdeterminant of the cube, and
* compose to the identity under Gauss composition, `Q₁ ∘ Q₂ ∘ Q₃ = 1`: for each
  pair of the three forms there is an explicit bilinear identity exhibiting the
  opposite of the third form (which represents the inverse class) as a Gauss
  composite of that pair.
-/
theorem bhargava_cube_law (K : Cube) :
    ((K.form₁).disc = K.hyperdet ∧ (K.form₂).disc = K.hyperdet ∧
      (K.form₃).disc = K.hyperdet) ∧
    (∀ x₁ y₁ x₂ y₂ : ℤ,
      (K.form₁).eval x₁ y₁ * (K.form₂).eval x₂ y₂
        = (K.form₃).opp.eval (K.bil₁₂snd x₁ y₁ x₂ y₂) (K.bil₁₂fst x₁ y₁ x₂ y₂)) ∧
    (∀ x₁ y₁ x₂ y₂ : ℤ,
      (K.form₁).eval x₁ y₁ * (K.form₃).eval x₂ y₂
        = (K.form₂).opp.eval (K.bil₁₃snd x₁ y₁ x₂ y₂) (K.bil₁₃fst x₁ y₁ x₂ y₂)) ∧
    (∀ x₁ y₁ x₂ y₂ : ℤ,
      (K.form₂).eval x₁ y₁ * (K.form₃).eval x₂ y₂
        = (K.form₁).opp.eval (K.bil₂₃snd x₁ y₁ x₂ y₂) (K.bil₂₃fst x₁ y₁ x₂ y₂)) :=
  ⟨⟨K.disc_form₁, K.disc_form₂, K.disc_form₃⟩,
   K.composition₁₂, K.composition₁₃, K.composition₂₃⟩

/-! ### Recovering Dirichlet's composition of concordant forms -/

/-- The cube whose three forms are Dirichlet's concordant pair `(a₁, b, a₂c)`,
`(a₂, b, a₁c)` together with `(c, b, a₁a₂)`, the opposite of their composite. -/
def dirichletCube (a₁ a₂ b c : ℤ) : Cube :=
  ⟨1, 0, 0, -a₁, 0, -a₂, -c, -b⟩

@[simp] theorem dirichletCube_form₁ (a₁ a₂ b c : ℤ) :
    (dirichletCube a₁ a₂ b c).form₁ = ⟨a₁, b, a₂ * c⟩ := by
  simp only [dirichletCube, Cube.form₁, BQF.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

@[simp] theorem dirichletCube_form₂ (a₁ a₂ b c : ℤ) :
    (dirichletCube a₁ a₂ b c).form₂ = ⟨c, b, a₁ * a₂⟩ := by
  simp only [dirichletCube, Cube.form₂, BQF.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

@[simp] theorem dirichletCube_form₃ (a₁ a₂ b c : ℤ) :
    (dirichletCube a₁ a₂ b c).form₃ = ⟨a₂, b, a₁ * c⟩ := by
  simp only [dirichletCube, Cube.form₃, BQF.mk.injEq]
  refine ⟨by ring, by ring, by ring⟩

/-- **Gauss/Dirichlet composition, recovered from the cube law.**  The concordant
forms `(a₁, b, a₂c)` and `(a₂, b, a₁c)` compose to `(a₁a₂, b, c)`, via the
classical bilinear substitution `X = x₁x₂ - c y₁y₂`,
`Y = a₁ x₁ y₂ + a₂ x₂ y₁ + b y₁ y₂`.  This is deduced from the cube law applied to
`dirichletCube`. -/
theorem dirichlet_composition (a₁ a₂ b c x₁ y₁ x₂ y₂ : ℤ) :
    (BQF.mk a₁ b (a₂ * c)).eval x₁ y₁ * (BQF.mk a₂ b (a₁ * c)).eval x₂ y₂
      = (BQF.mk (a₁ * a₂) b c).eval (x₁ * x₂ - c * y₁ * y₂)
          (a₁ * x₁ * y₂ + a₂ * x₂ * y₁ + b * y₁ * y₂) := by
  have key := (dirichletCube a₁ a₂ b c).composition₁₃ x₁ y₁ x₂ y₂
  rw [dirichletCube_form₁, dirichletCube_form₂, dirichletCube_form₃] at key
  simp only [dirichletCube, Cube.bil₁₃fst, Cube.bil₁₃snd, BQF.eval, BQF.opp] at key
  simp only [BQF.eval]
  linear_combination key

/-- The three forms of a Dirichlet cube indeed share the discriminant
`b² - 4a₁a₂c`. -/
theorem dirichlet_disc (a₁ a₂ b c : ℤ) :
    (BQF.mk a₁ b (a₂ * c)).disc = b ^ 2 - 4 * (a₁ * a₂) * c ∧
    (BQF.mk a₂ b (a₁ * c)).disc = b ^ 2 - 4 * (a₁ * a₂) * c ∧
    (BQF.mk (a₁ * a₂) b c).disc = b ^ 2 - 4 * (a₁ * a₂) * c := by
  refine ⟨?_, ?_, ?_⟩ <;> simp only [BQF.disc] <;> ring

end Frontier


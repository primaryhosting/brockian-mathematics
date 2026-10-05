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
def disc (q : BQF) : ℤ := q.B ^ 2 - 4 * q.A * q.C

/-- Evaluation of a binary quadratic form. -/
def eval (q : BQF) (x y : ℤ) : ℤ := q.A * x ^ 2 + q.B * x * y + q.C * y ^ 2

/-- The opposite form `(A, -B, C)`; its class is the inverse of the class of `q`. -/
def opposite (q : BQF) : BQF := ⟨q.A, -q.B, q.C⟩

@[simp] lemma opposite_disc (q : BQF) : q.opposite.disc = q.disc := by
  simp [disc, opposite]

end BQF

/-- The principal (identity) form of discriminant `D`: it is `(1, 0, -D/4)` when `D` is even
and `(1, 1, (1 - D)/4)` when `D` is odd. -/
def principalForm (D : ℤ) : BQF :=
  if D % 2 = 0 then ⟨1, 0, -(D / 4)⟩ else ⟨1, 1, (1 - D) / 4⟩

/-- A *Bhargava cube*: an element of `ℤ² ⊗ ℤ² ⊗ ℤ²`, recorded by its eight integer entries.
The entries are placed on the cube so that `(a, b, c, d)` is the front face and
`(e, f, g, h)` the back face. -/
structure Cube where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  g : ℤ
  h : ℤ

namespace Cube

variable (K : Cube)

/-- First slicing of the cube: front face. -/
def M₁ : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.b; K.c, K.d]
/-- First slicing of the cube: back face. -/
def N₁ : Matrix (Fin 2) (Fin 2) ℤ := !![K.e, K.f; K.g, K.h]
/-- Second slicing of the cube: top face. -/
def M₂ : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.c; K.e, K.g]
/-- Second slicing of the cube: bottom face. -/
def N₂ : Matrix (Fin 2) (Fin 2) ℤ := !![K.b, K.d; K.f, K.h]
/-- Third slicing of the cube: left face. -/
def M₃ : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.e; K.b, K.f]
/-- Third slicing of the cube: right face. -/
def N₃ : Matrix (Fin 2) (Fin 2) ℤ := !![K.c, K.g; K.d, K.h]

/-- The first quadratic form of the cube, `Q₁(x, y) = -det (x M₁ + y N₁)`. -/
def Q₁ : BQF :=
  ⟨K.b * K.c - K.a * K.d,
   K.b * K.g + K.c * K.f - K.a * K.h - K.d * K.e,
   K.f * K.g - K.e * K.h⟩

/-- The second quadratic form of the cube, `Q₂(x, y) = -det (x M₂ + y N₂)`. -/
def Q₂ : BQF :=
  ⟨K.c * K.e - K.a * K.g,
   K.c * K.f + K.d * K.e - K.a * K.h - K.b * K.g,
   K.d * K.f - K.b * K.h⟩

/-- The third quadratic form of the cube, `Q₃(x, y) = -det (x M₃ + y N₃)`. -/
def Q₃ : BQF :=
  ⟨K.b * K.e - K.a * K.f,
   K.b * K.g + K.d * K.e - K.a * K.h - K.c * K.f,
   K.d * K.g - K.c * K.h⟩

/-- The discriminant of a Bhargava cube. -/
def disc : ℤ :=
  (K.a * K.h + K.d * K.e - K.b * K.g - K.c * K.f) ^ 2
    - 4 * (K.a * K.d - K.b * K.c) * (K.e * K.h - K.f * K.g)

end Cube

/-! ### The three forms are the negated determinants of the three slice pencils -/

lemma Cube.Q₁_eval (K : Cube) (x y : ℤ) :
    K.Q₁.eval x y = -(x • K.M₁ + y • K.N₁).det := by
  simp [Cube.Q₁, Cube.M₁, Cube.N₁, BQF.eval, Matrix.det_fin_two]
  ring

lemma Cube.Q₂_eval (K : Cube) (x y : ℤ) :
    K.Q₂.eval x y = -(x • K.M₂ + y • K.N₂).det := by
  simp [Cube.Q₂, Cube.M₂, Cube.N₂, BQF.eval, Matrix.det_fin_two]
  ring

lemma Cube.Q₃_eval (K : Cube) (x y : ℤ) :
    K.Q₃.eval x y = -(x • K.M₃ + y • K.N₃).det := by
  simp [Cube.Q₃, Cube.M₃, Cube.N₃, BQF.eval, Matrix.det_fin_two]
  ring

/-! ### The three forms share the discriminant of the cube -/

lemma Cube.Q₁_disc (K : Cube) : K.Q₁.disc = K.disc := by
  simp [Cube.Q₁, Cube.disc, BQF.disc]; ring

lemma Cube.Q₂_disc (K : Cube) : K.Q₂.disc = K.disc := by
  simp [Cube.Q₂, Cube.disc, BQF.disc]; ring

lemma Cube.Q₃_disc (K : Cube) : K.Q₃.disc = K.disc := by
  simp [Cube.Q₃, Cube.disc, BQF.disc]; ring

/-! ### The identity (base) case of the cube law -/

/-- For every form `q` there is a cube whose three forms are the principal form of
discriminant `disc q`, the form `q` itself, and the opposite form of `q`.  Via the cube law
this is the statement that `[q] * [q]⁻¹` is the identity class. -/
lemma exists_cube_principal (q : BQF) :
    ∃ K : Cube, K.Q₁ = principalForm q.disc ∧ K.Q₂ = q ∧ K.Q₃ = q.opposite := by
  rcases Int.even_or_odd q.B with ⟨k, hk⟩ | ⟨k, hk⟩
  · -- `q.B = k + k` is even; take `f = k`, `g = -k`.
    refine ⟨⟨0, 1, 1, 0, q.A, k, -k, -q.C⟩, ?_, ?_, ?_⟩
    · have hD : q.disc = 4 * (k ^ 2 - q.A * q.C) := by
        simp only [BQF.disc, hk]; ring
      obtain ⟨m, hm⟩ : ∃ m : ℤ, q.disc = 4 * m := ⟨_, hD⟩
      have hmk : m = k ^ 2 - q.A * q.C := by linarith
      have hpar : q.disc % 2 = 0 := by omega
      have hdiv : q.disc / 4 = m := by omega
      rw [principalForm, if_pos hpar, hdiv, hmk, Cube.Q₁]
      simp only [BQF.mk.injEq]
      refine ⟨by ring, by ring, by ring⟩
    · simp only [Cube.Q₂]
      refine BQF.mk.injEq .. ▸ ⟨by ring, by rw [hk]; ring, by ring⟩
    · simp only [Cube.Q₃, BQF.opposite]
      refine BQF.mk.injEq .. ▸ ⟨by ring, by rw [hk]; ring, by ring⟩
  · -- `q.B = 2 * k + 1` is odd; take `f = k + 1`, `g = -k`.
    refine ⟨⟨0, 1, 1, 0, q.A, k + 1, -k, -q.C⟩, ?_, ?_, ?_⟩
    · have hD : q.disc = 4 * (k ^ 2 + k - q.A * q.C) + 1 := by
        simp only [BQF.disc, hk]; ring
      obtain ⟨m, hm⟩ : ∃ m : ℤ, q.disc = 4 * m + 1 := ⟨_, hD⟩
      have hmk : m = k ^ 2 + k - q.A * q.C := by linarith
      have hpar : ¬ (q.disc % 2 = 0) := by omega
      have hdiv : (1 - q.disc) / 4 = -m := by omega
      rw [principalForm, if_neg hpar, hdiv, hmk, Cube.Q₁]
      simp only [BQF.mk.injEq]
      refine ⟨by ring, by ring, by ring⟩
    · simp only [Cube.Q₂]
      refine BQF.mk.injEq .. ▸ ⟨by ring, by rw [hk]; ring, by ring⟩
    · simp only [Cube.Q₃, BQF.opposite]
      refine BQF.mk.injEq .. ▸ ⟨by ring, by rw [hk]; ring, by ring⟩

/-! ### Gauss/Dirichlet composition arises from a cube -/

/-- The cube realizing Dirichlet's composition of the two concordant forms
`(a₁, b, a₂ c)` and `(a₂, b, a₁ c)`, whose composite is `(a₁ a₂, b, c)`. -/
def dirichletCube (a₁ a₂ b c : ℤ) : Cube := ⟨0, a₁, 1, 0, a₂, b, 0, -c⟩

lemma dirichletCube_Q₁ (a₁ a₂ b c : ℤ) : (dirichletCube a₁ a₂ b c).Q₁ = ⟨a₁, b, a₂ * c⟩ := by
  simp only [dirichletCube, Cube.Q₁]
  refine BQF.mk.injEq .. ▸ ⟨by ring, by ring, by ring⟩

lemma dirichletCube_Q₂ (a₁ a₂ b c : ℤ) : (dirichletCube a₁ a₂ b c).Q₂ = ⟨a₂, b, a₁ * c⟩ := by
  simp only [dirichletCube, Cube.Q₂]
  refine BQF.mk.injEq .. ▸ ⟨by ring, by ring, by ring⟩

lemma dirichletCube_Q₃ (a₁ a₂ b c : ℤ) :
    (dirichletCube a₁ a₂ b c).Q₃ = (BQF.mk (a₁ * a₂) b c).opposite := by
  simp only [dirichletCube, Cube.Q₃, BQF.opposite]
  refine BQF.mk.injEq .. ▸ ⟨by ring, by ring, by ring⟩

/-! ### Covariance under the action of `SL₂(ℤ) × SL₂(ℤ) × SL₂(ℤ)` -/

namespace Cube

/-- The action of `γ = !![p, q; r, s]` on the first tensor factor: it replaces the pencil
`(M₁, N₁)` by `(p M₁ + q N₁, r M₁ + s N₁)`. -/
def actFirst (K : Cube) (p q r s : ℤ) : Cube :=
  ⟨p * K.a + q * K.e, p * K.b + q * K.f, p * K.c + q * K.g, p * K.d + q * K.h,
   r * K.a + s * K.e, r * K.b + s * K.f, r * K.c + s * K.g, r * K.d + s * K.h⟩

/-- The action of `γ = !![p, q; r, s]` on the second tensor factor. -/
def actSecond (K : Cube) (p q r s : ℤ) : Cube :=
  ⟨p * K.a + q * K.b, r * K.a + s * K.b, p * K.c + q * K.d, r * K.c + s * K.d,
   p * K.e + q * K.f, r * K.e + s * K.f, p * K.g + q * K.h, r * K.g + s * K.h⟩

/-- The action of `γ = !![p, q; r, s]` on the third tensor factor. -/
def actThird (K : Cube) (p q r s : ℤ) : Cube :=
  ⟨p * K.a + q * K.c, p * K.b + q * K.d, r * K.a + s * K.c, r * K.b + s * K.d,
   p * K.e + q * K.g, p * K.f + q * K.h, r * K.e + s * K.g, r * K.f + s * K.h⟩

lemma actFirst_disc (K : Cube) (p q r s : ℤ) :
    (K.actFirst p q r s).disc = (p * s - q * r) ^ 2 * K.disc := by
  simp only [actFirst, disc]; ring

lemma actFirst_Q₁_eval (K : Cube) (p q r s x y : ℤ) :
    (K.actFirst p q r s).Q₁.eval x y = K.Q₁.eval (p * x + r * y) (q * x + s * y) := by
  simp only [actFirst, Q₁, BQF.eval]; ring

lemma actSecond_Q₂_eval (K : Cube) (p q r s x y : ℤ) :
    (K.actSecond p q r s).Q₂.eval x y = K.Q₂.eval (p * x + r * y) (q * x + s * y) := by
  simp only [actSecond, Q₂, BQF.eval]; ring

lemma actThird_Q₃_eval (K : Cube) (p q r s x y : ℤ) :
    (K.actThird p q r s).Q₃.eval x y = K.Q₃.eval (p * x + r * y) (q * x + s * y) := by
  simp only [actThird, Q₃, BQF.eval]; ring

lemma actFirst_Q₂ (K : Cube) {p q r s : ℤ} (hdet : p * s - q * r = 1) :
    (K.actFirst p q r s).Q₂ = K.Q₂ := by
  simp only [actFirst, Q₂, BQF.mk.injEq]
  refine ⟨by linear_combination (K.c * K.e - K.a * K.g) * hdet,
    by linear_combination (K.c * K.f + K.d * K.e - K.a * K.h - K.b * K.g) * hdet,
    by linear_combination (K.d * K.f - K.b * K.h) * hdet⟩

lemma actFirst_Q₃ (K : Cube) {p q r s : ℤ} (hdet : p * s - q * r = 1) :
    (K.actFirst p q r s).Q₃ = K.Q₃ := by
  simp only [actFirst, Q₃, BQF.mk.injEq]
  refine ⟨by linear_combination (K.b * K.e - K.a * K.f) * hdet,
    by linear_combination (K.b * K.g + K.d * K.e - K.a * K.h - K.c * K.f) * hdet,
    by linear_combination (K.d * K.g - K.c * K.h) * hdet⟩

lemma actSecond_Q₁ (K : Cube) {p q r s : ℤ} (hdet : p * s - q * r = 1) :
    (K.actSecond p q r s).Q₁ = K.Q₁ := by
  simp only [actSecond, Q₁, BQF.mk.injEq]
  refine ⟨by linear_combination (K.b * K.c - K.a * K.d) * hdet,
    by linear_combination (K.b * K.g + K.c * K.f - K.a * K.h - K.d * K.e) * hdet,
    by linear_combination (K.f * K.g - K.e * K.h) * hdet⟩

lemma actSecond_Q₃ (K : Cube) {p q r s : ℤ} (hdet : p * s - q * r = 1) :
    (K.actSecond p q r s).Q₃ = K.Q₃ := by
  simp only [actSecond, Q₃, BQF.mk.injEq]
  refine ⟨by linear_combination (K.b * K.e - K.a * K.f) * hdet,
    by linear_combination (K.b * K.g + K.d * K.e - K.a * K.h - K.c * K.f) * hdet,
    by linear_combination (K.d * K.g - K.c * K.h) * hdet⟩

lemma actThird_Q₁ (K : Cube) {p q r s : ℤ} (hdet : p * s - q * r = 1) :
    (K.actThird p q r s).Q₁ = K.Q₁ := by
  simp only [actThird, Q₁, BQF.mk.injEq]
  refine ⟨by linear_combination (K.b * K.c - K.a * K.d) * hdet,
    by linear_combination (K.b * K.g + K.c * K.f - K.a * K.h - K.d * K.e) * hdet,
    by linear_combination (K.f * K.g - K.e * K.h) * hdet⟩

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
theorem bhargava_cube_law :
    (∀ (K : Cube) (x y : ℤ),
        K.Q₁.eval x y = -(x • K.M₁ + y • K.N₁).det ∧
        K.Q₂.eval x y = -(x • K.M₂ + y • K.N₂).det ∧
        K.Q₃.eval x y = -(x • K.M₃ + y • K.N₃).det) ∧
    (∀ K : Cube, K.Q₁.disc = K.disc ∧ K.Q₂.disc = K.disc ∧ K.Q₃.disc = K.disc) ∧
    (∀ q : BQF, ∃ K : Cube,
        K.Q₁ = principalForm q.disc ∧ K.Q₂ = q ∧ K.Q₃ = q.opposite) ∧
    (∀ a₁ a₂ b c : ℤ, ∃ K : Cube,
        K.Q₁ = ⟨a₁, b, a₂ * c⟩ ∧ K.Q₂ = ⟨a₂, b, a₁ * c⟩ ∧
        K.Q₃ = (BQF.mk (a₁ * a₂) b c).opposite) ∧
    (∀ (K : Cube) (p q r s : ℤ), p * s - q * r = 1 →
        ((∀ x y : ℤ, (K.actFirst p q r s).Q₁.eval x y
            = K.Q₁.eval (p * x + r * y) (q * x + s * y)) ∧
          (K.actFirst p q r s).Q₂ = K.Q₂ ∧ (K.actFirst p q r s).Q₃ = K.Q₃) ∧
        ((∀ x y : ℤ, (K.actSecond p q r s).Q₂.eval x y
            = K.Q₂.eval (p * x + r * y) (q * x + s * y)) ∧
          (K.actSecond p q r s).Q₁ = K.Q₁ ∧ (K.actSecond p q r s).Q₃ = K.Q₃) ∧
        ((∀ x y : ℤ, (K.actThird p q r s).Q₃.eval x y
            = K.Q₃.eval (p * x + r * y) (q * x + s * y)) ∧
          (K.actThird p q r s).Q₁ = K.Q₁ ∧ (K.actThird p q r s).Q₂ = K.Q₂)) := by
  refine ⟨fun K x y => ⟨K.Q₁_eval x y, K.Q₂_eval x y, K.Q₃_eval x y⟩,
    fun K => ⟨K.Q₁_disc, K.Q₂_disc, K.Q₃_disc⟩, exists_cube_principal,
    fun a₁ a₂ b c => ⟨dirichletCube a₁ a₂ b c,
      dirichletCube_Q₁ a₁ a₂ b c, dirichletCube_Q₂ a₁ a₂ b c, dirichletCube_Q₃ a₁ a₂ b c⟩,
    fun K p q r s hdet =>
      ⟨⟨K.actFirst_Q₁_eval p q r s, K.actFirst_Q₂ hdet, K.actFirst_Q₃ hdet⟩,
       ⟨K.actSecond_Q₂_eval p q r s, K.actSecond_Q₁ hdet, K.actSecond_Q₃ hdet⟩,
       ⟨K.actThird_Q₃_eval p q r s, K.actThird_Q₁ hdet, K.actThird_Q₂ hdet⟩⟩⟩

end Frontier


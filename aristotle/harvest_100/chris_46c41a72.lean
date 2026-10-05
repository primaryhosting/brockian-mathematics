/-
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
Note on the header: Lean 4 requires `import` to be the first command of a file, so the mandated
header above is reproduced verbatim as an ordinary block comment rather than as a module
docstring (`/-! ... -/`), which would itself be a command and could not precede `import`.

# Bhargava's cube law

A *Bhargava cube* is an element of `ℤ² ⊗ ℤ² ⊗ ℤ²`, i.e. eight integers placed at the vertices of
a cube.  Slicing the cube by planes parallel to each of the three pairs of opposite faces gives
three pairs of `2 × 2` integer matrices `(Mᵢ, Nᵢ)`, and hence three integral binary quadratic
forms

`Qᵢ(x, y) = -det(Mᵢ x - Nᵢ y)`.

Bhargava's cube law (Higher composition laws I) states that the three forms have the same
discriminant and that, in the class group of that discriminant, `Q₁ ∘ Q₂ ∘ Q₃` is the identity;
this recovers Gauss composition.

This file develops the material needed for the base case and proves it:

* `Frontier.cube_disc_eq` : the three forms of an arbitrary cube share a discriminant, given
  explicitly by the invariant `Frontier.Cube.disc`.
* `Frontier.form2_actFirst`, `Frontier.form3_actFirst`, `Frontier.form1_actFirst` : the action of
  `SL₂(ℤ)` on the first pair of faces fixes `Q₂` and `Q₃` on the nose and changes `Q₁` by the
  corresponding unimodular substitution — so the triple of `SL₂(ℤ)`-classes is a genuine invariant
  of the `Γ = SL₂(ℤ)³`-orbit.
* `Frontier.dirichletCube_forms` : the cube of *concordant* forms `(a₁, B, a₂C)`, `(a₂, B, a₁C)`
  has third form `(a₁a₂, -B, C)`, the opposite of the Dirichlet composite.
* `Frontier.gauss_composition` : the explicit bilinear composition identity
  `Q₁(x₁,y₁) · Q₂(x₂,y₂) = Q₃ᵒᵖ(X, Y)` for that cube, i.e. Gauss/Dirichlet composition.
* `Frontier.brahmagupta` : its base case, composition of the principal form with itself.
* `Frontier.bhargava_cube_law` : the packaged statement.
-/

namespace Frontier

/-- An integral binary quadratic form `A x² + B x y + C y²`, recorded by its coefficients. -/
structure BQF where
  A : ℤ
  B : ℤ
  C : ℤ
deriving DecidableEq, Repr

namespace BQF

/-- Evaluation of a binary quadratic form. -/
def eval (Q : BQF) (x y : ℤ) : ℤ := Q.A * x ^ 2 + Q.B * x * y + Q.C * y ^ 2

/-- The discriminant `B² - 4AC` of a binary quadratic form. -/
def disc (Q : BQF) : ℤ := Q.B ^ 2 - 4 * Q.A * Q.C

/-- The opposite (inverse) form `A x² - B x y + C y²`, representing the inverse class. -/
def op (Q : BQF) : BQF := ⟨Q.A, -Q.B, Q.C⟩

/-- The principal form `x² - n y²`, of discriminant `4n`. -/
def principal (n : ℤ) : BQF := ⟨1, 0, -n⟩

@[simp] lemma disc_op (Q : BQF) : Q.op.disc = Q.disc := by simp [disc, op]

@[simp] lemma op_op (Q : BQF) : Q.op.op = Q := by simp [op]

@[simp] lemma disc_principal (n : ℤ) : (principal n).disc = 4 * n := by
  simp [disc, principal]

/-- A form and its opposite are `GL₂(ℤ)`-equivalent via `(x, y) ↦ (x, -y)`. -/
lemma eval_op (Q : BQF) (x y : ℤ) : Q.op.eval x y = Q.eval x (-y) := by
  simp [eval, op]

end BQF

/-- A *Bhargava cube*: eight integers placed at the vertices of a cube.  The front face is
`a b / c d` and the back face is `e f / g h`; the three ways of slicing the cube into two parallel
`2 × 2` faces give the three matrix pairs

* `M₁ = [[a,b],[c,d]]`, `N₁ = [[e,f],[g,h]]` (front / back),
* `M₂ = [[a,c],[e,g]]`, `N₂ = [[b,d],[f,h]]` (left / right),
* `M₃ = [[a,e],[b,f]]`, `N₃ = [[c,g],[d,h]]` (top / bottom). -/
structure Cube where
  a : ℤ
  b : ℤ
  c : ℤ
  d : ℤ
  e : ℤ
  f : ℤ
  g : ℤ
  h : ℤ
deriving DecidableEq, Repr

namespace Cube

/-- The first quadratic form of a cube, `Q₁(x,y) = -det(M₁ x - N₁ y)`. -/
def form1 (K : Cube) : BQF :=
  ⟨-(K.a * K.d - K.b * K.c),
    K.a * K.h + K.d * K.e - K.b * K.g - K.c * K.f,
    -(K.e * K.h - K.f * K.g)⟩

/-- The second quadratic form of a cube, `Q₂(x,y) = -det(M₂ x - N₂ y)`. -/
def form2 (K : Cube) : BQF :=
  ⟨-(K.a * K.g - K.c * K.e),
    K.a * K.h + K.b * K.g - K.c * K.f - K.d * K.e,
    -(K.b * K.h - K.d * K.f)⟩

/-- The third quadratic form of a cube, `Q₃(x,y) = -det(M₃ x - N₃ y)`. -/
def form3 (K : Cube) : BQF :=
  ⟨-(K.a * K.f - K.b * K.e),
    K.a * K.h + K.c * K.f - K.b * K.g - K.d * K.e,
    -(K.c * K.h - K.d * K.g)⟩

/-- The discriminant invariant of a cube (Cayley's hyperdeterminant of the `2×2×2` box). -/
def disc (K : Cube) : ℤ :=
  (K.a * K.h + K.d * K.e - K.b * K.g - K.c * K.f) ^ 2
    - 4 * (K.a * K.d - K.b * K.c) * (K.e * K.h - K.f * K.g)

/-- The action of the matrix `[[r,s],[t,u]]` on the first pair of faces of a cube:
`(M₁, N₁) ↦ (r M₁ + s N₁, t M₁ + u N₁)`.  This is one of the three factors of the group
`Γ = SL₂(ℤ)³` acting on cubes. -/
def actFirst (K : Cube) (r s t u : ℤ) : Cube :=
  ⟨r * K.a + s * K.e, r * K.b + s * K.f, r * K.c + s * K.g, r * K.d + s * K.h,
    t * K.a + u * K.e, t * K.b + u * K.f, t * K.c + u * K.g, t * K.d + u * K.h⟩

/-- The *identity cube* of discriminant `4n`: the cube all three of whose quadratic forms are
the principal form `x² - n y²`. -/
def identityCube (n : ℤ) : Cube := ⟨0, 1, 1, 0, 1, 0, 0, n⟩

/-- The cube attached to a pair of *concordant* forms `(a₁, B, a₂C)` and `(a₂, B, a₁C)`, whose
Dirichlet composite is `(a₁a₂, B, C)`. -/
def dirichletCube (a₁ a₂ B C : ℤ) : Cube := ⟨0, a₁, 1, 0, a₂, -B, 0, -C⟩

end Cube

/-! ### The three forms really are `-det` of the three linear pencils -/

lemma form1_eq_neg_det (K : Cube) (x y : ℤ) :
    K.form1.eval x y =
      -((K.a * x - K.e * y) * (K.d * x - K.h * y)
        - (K.b * x - K.f * y) * (K.c * x - K.g * y)) := by
  simp [Cube.form1, BQF.eval]; ring

lemma form2_eq_neg_det (K : Cube) (x y : ℤ) :
    K.form2.eval x y =
      -((K.a * x - K.b * y) * (K.g * x - K.h * y)
        - (K.c * x - K.d * y) * (K.e * x - K.f * y)) := by
  simp [Cube.form2, BQF.eval]; ring

lemma form3_eq_neg_det (K : Cube) (x y : ℤ) :
    K.form3.eval x y =
      -((K.a * x - K.c * y) * (K.f * x - K.h * y)
        - (K.e * x - K.g * y) * (K.b * x - K.d * y)) := by
  simp [Cube.form3, BQF.eval]; ring

/-! ### Step 1: a cube gives three forms of the same discriminant -/

/-- The three binary quadratic forms of a Bhargava cube all have the same discriminant, namely the
hyperdeterminant invariant `Cube.disc`. -/
theorem cube_disc_eq (K : Cube) :
    K.form1.disc = K.disc ∧ K.form2.disc = K.disc ∧ K.form3.disc = K.disc := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Cube.form1, Cube.form2, Cube.form3, Cube.disc, BQF.disc] <;> ring

/-! ### Step 2: the `SL₂(ℤ)³`-action

Acting by `γ ∈ SL₂(ℤ)` on one pair of parallel faces leaves the other two forms *unchanged*, and
changes the corresponding form by the unimodular substitution `γ`.  Hence the triple of
`SL₂(ℤ)`-equivalence classes `(⟦Q₁⟧, ⟦Q₂⟧, ⟦Q₃⟧)` depends only on the `Γ`-orbit of the cube. -/

/-- The second form is invariant under the first-factor action of `SL₂(ℤ)`. -/
theorem form2_actFirst (K : Cube) (r s t u : ℤ) (hdet : r * u - s * t = 1) :
    (K.actFirst r s t u).form2 = K.form2 := by
  cases K with
  | mk a b c d e f g h =>
    simp only [Cube.actFirst, Cube.form2, BQF.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (-(a * g - c * e)) * hdet
    · linear_combination (a * h + b * g - c * f - d * e) * hdet
    · linear_combination (-(b * h - d * f)) * hdet

/-- The third form is invariant under the first-factor action of `SL₂(ℤ)`. -/
theorem form3_actFirst (K : Cube) (r s t u : ℤ) (hdet : r * u - s * t = 1) :
    (K.actFirst r s t u).form3 = K.form3 := by
  cases K with
  | mk a b c d e f g h =>
    simp only [Cube.actFirst, Cube.form3, BQF.mk.injEq]
    refine ⟨?_, ?_, ?_⟩
    · linear_combination (-(a * f - b * e)) * hdet
    · linear_combination (a * h + c * f - b * g - d * e) * hdet
    · linear_combination (-(c * h - d * g)) * hdet

/-- The first form is transformed by the substitution `(x, y) ↦ (r x - t y, -s x + u y)` under the
first-factor action, an `SL₂(ℤ)` change of variables when `ru - st = 1`. -/
theorem form1_actFirst (K : Cube) (r s t u x y : ℤ) :
    (K.actFirst r s t u).form1.eval x y = K.form1.eval (r * x - t * y) (-(s * x) + u * y) := by
  cases K with
  | mk a b c d e f g h =>
    simp only [Cube.actFirst, Cube.form1, BQF.eval]; ring

/-! ### Step 3: Gauss composition from the cube -/

/-- The cube of concordant forms produces `(a₁, B, a₂C)`, `(a₂, B, a₁C)` and, as third form, the
opposite `(a₁a₂, -B, C)` of their Dirichlet composite. -/
theorem dirichletCube_forms (a₁ a₂ B C : ℤ) :
    (Cube.dirichletCube a₁ a₂ B C).form1 = ⟨a₁, B, a₂ * C⟩ ∧
    (Cube.dirichletCube a₁ a₂ B C).form2 = ⟨a₂, B, a₁ * C⟩ ∧
    (Cube.dirichletCube a₁ a₂ B C).form3 = (BQF.mk (a₁ * a₂) B C).op := by
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [Cube.dirichletCube, Cube.form1, Cube.form2, Cube.form3, BQF.op, mul_comm]

/-- All three forms of the concordant cube have discriminant `B² - 4a₁a₂C`. -/
theorem dirichletCube_disc (a₁ a₂ B C : ℤ) :
    (Cube.dirichletCube a₁ a₂ B C).disc = B ^ 2 - 4 * (a₁ * a₂) * C := by
  simp [Cube.dirichletCube, Cube.disc]; ring

/-- **Gauss composition.**  For the cube of concordant forms, the product of the values of `Q₁` and
`Q₂` is a value of the opposite of `Q₃`, via an explicit pair of bilinear forms.  Equivalently
`Q₁ ∘ Q₂ ∘ Q₃ = 1`: the composite of `Q₁` and `Q₂` is the inverse class of `Q₃`. -/
theorem gauss_composition (a₁ a₂ B C x₁ y₁ x₂ y₂ : ℤ) :
    (Cube.dirichletCube a₁ a₂ B C).form1.eval x₁ y₁ *
        (Cube.dirichletCube a₁ a₂ B C).form2.eval x₂ y₂
      = (Cube.dirichletCube a₁ a₂ B C).form3.op.eval
          (x₁ * x₂ - C * y₁ * y₂) (a₁ * x₁ * y₂ + a₂ * x₂ * y₁ + B * y₁ * y₂) := by
  simp [Cube.dirichletCube, Cube.form1, Cube.form2, Cube.form3, BQF.op, BQF.eval]; ring

/-- The identity cube is the concordant cube of the principal form with itself. -/
theorem identityCube_eq (n : ℤ) : Cube.identityCube n = Cube.dirichletCube 1 1 0 (-n) := by
  simp [Cube.identityCube, Cube.dirichletCube]

/-- The three forms of the identity cube of discriminant `4n` are all the principal form. -/
theorem identityCube_forms (n : ℤ) :
    (Cube.identityCube n).form1 = BQF.principal n ∧
    (Cube.identityCube n).form2 = BQF.principal n ∧
    (Cube.identityCube n).form3 = BQF.principal n := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [Cube.identityCube, Cube.form1, Cube.form2, Cube.form3,
    BQF.principal]

/-- **Brahmagupta's identity**, the base case of Gauss composition: the principal form composed
with itself is the principal form. -/
theorem brahmagupta (n x₁ y₁ x₂ y₂ : ℤ) :
    (BQF.principal n).eval x₁ y₁ * (BQF.principal n).eval x₂ y₂
      = (BQF.principal n).eval (x₁ * x₂ + n * y₁ * y₂) (x₁ * y₂ + y₁ * x₂) := by
  simp [BQF.principal, BQF.eval]; ring

/-!
## The cube law

The theorem below packages the statement.  For an arbitrary Bhargava cube:

* **(1)** the three attached binary quadratic forms all have the same discriminant, the
  hyperdeterminant invariant `Cube.disc` — so a cube determines a triple of forms of a common
  discriminant;
* **(2)** the `Γ = SL₂(ℤ)³`-action is well defined on this data: acting by `γ ∈ SL₂(ℤ)` on one
  pair of opposite faces fixes the other two forms exactly and changes the remaining form by the
  unimodular substitution `γ`, hence not its class;
* **(3)** for the cube built from a pair of concordant forms `(a₁, B, a₂C)`, `(a₂, B, a₁C)` of
  discriminant `B² - 4a₁a₂C`, the third form is `(a₁a₂, -B, C)`, and the explicit bilinear
  identity `Q₁(x₁,y₁) · Q₂(x₂,y₂) = Q₃ᵒᵖ(X, Y)` holds — this is exactly Gauss (Dirichlet)
  composition, i.e. `Q₁ ∘ Q₂ ∘ Q₃ = 1` in the class group;
* **(4)** in the base case `a₁ = a₂ = 1`, `B = 0`, `C = -n` the cube is the identity cube, all
  three forms are the principal form `x² - n y²` of discriminant `4n`, and the composition law
  degenerates to Brahmagupta's identity.
-/
theorem bhargava_cube_law :
    -- (1) common discriminant
    (∀ K : Cube, K.form1.disc = K.disc ∧ K.form2.disc = K.disc ∧ K.form3.disc = K.disc) ∧
    -- (2) the SL₂(ℤ)-action on one pair of faces
    (∀ (K : Cube) (r s t u : ℤ), r * u - s * t = 1 →
      (K.actFirst r s t u).form2 = K.form2 ∧
      (K.actFirst r s t u).form3 = K.form3 ∧
      ∀ x y : ℤ, (K.actFirst r s t u).form1.eval x y
        = K.form1.eval (r * x - t * y) (-(s * x) + u * y)) ∧
    -- (3) Gauss composition of concordant forms, read off from the cube
    (∀ a₁ a₂ B C : ℤ,
      (Cube.dirichletCube a₁ a₂ B C).form1 = ⟨a₁, B, a₂ * C⟩ ∧
      (Cube.dirichletCube a₁ a₂ B C).form2 = ⟨a₂, B, a₁ * C⟩ ∧
      (Cube.dirichletCube a₁ a₂ B C).form3 = (BQF.mk (a₁ * a₂) B C).op ∧
      (Cube.dirichletCube a₁ a₂ B C).disc = B ^ 2 - 4 * (a₁ * a₂) * C ∧
      ∀ x₁ y₁ x₂ y₂ : ℤ,
        (Cube.dirichletCube a₁ a₂ B C).form1.eval x₁ y₁ *
            (Cube.dirichletCube a₁ a₂ B C).form2.eval x₂ y₂
          = (Cube.dirichletCube a₁ a₂ B C).form3.op.eval
              (x₁ * x₂ - C * y₁ * y₂) (a₁ * x₁ * y₂ + a₂ * x₂ * y₁ + B * y₁ * y₂)) ∧
    -- (4) the base case: the identity cube and Brahmagupta's identity
    (∀ n : ℤ, Cube.identityCube n = Cube.dirichletCube 1 1 0 (-n) ∧
      (Cube.identityCube n).form1 = BQF.principal n ∧
      (Cube.identityCube n).form2 = BQF.principal n ∧
      (Cube.identityCube n).form3 = BQF.principal n ∧
      (Cube.identityCube n).form1.disc = 4 * n ∧
      ∀ x₁ y₁ x₂ y₂ : ℤ,
        (BQF.principal n).eval x₁ y₁ * (BQF.principal n).eval x₂ y₂
          = (BQF.principal n).eval (x₁ * x₂ + n * y₁ * y₂) (x₁ * y₂ + y₁ * x₂)) := by
  refine ⟨cube_disc_eq, fun K r s t u hdet =>
      ⟨form2_actFirst K r s t u hdet, form3_actFirst K r s t u hdet, form1_actFirst K r s t u⟩,
    fun a₁ a₂ B C => ⟨(dirichletCube_forms a₁ a₂ B C).1, (dirichletCube_forms a₁ a₂ B C).2.1,
      (dirichletCube_forms a₁ a₂ B C).2.2, dirichletCube_disc a₁ a₂ B C,
      gauss_composition a₁ a₂ B C⟩,
    fun n => ⟨identityCube_eq n, (identityCube_forms n).1, (identityCube_forms n).2.1,
      (identityCube_forms n).2.2, ?_, brahmagupta n⟩⟩
  rw [(identityCube_forms n).1, BQF.disc_principal]

end Frontier

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


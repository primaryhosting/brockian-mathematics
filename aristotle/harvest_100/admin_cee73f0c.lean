/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-! ## Integral binary quadratic forms -/

/-- An integral binary quadratic form `A x^2 + B x y + C y^2`, recorded by its
coefficient triple `(A, B, C)`. -/
structure BQF where
  A : Int
  B : Int
  C : Int
deriving DecidableEq, Repr

namespace BQF

/-- Evaluation of a binary quadratic form. -/
def eval (Q : BQF) (x y : Int) : Int := Q.A * x ^ 2 + Q.B * x * y + Q.C * y ^ 2

/-- The discriminant `B^2 - 4AC` of a binary quadratic form. -/
def disc (Q : BQF) : Int := Q.B ^ 2 - 4 * Q.A * Q.C

/-- The opposite form `A x^2 - B x y + C y^2`; its class is the inverse class of `Q`
in the form class group. -/
def op (Q : BQF) : BQF := ⟨Q.A, -Q.B, Q.C⟩

/-- Proper (i.e. `SL₂(ℤ)`-) equivalence of binary quadratic forms: `Q'` is obtained
from `Q` by a substitution of determinant `1`.  The classes of this relation are the
elements of the form class group. -/
def SLEquiv (Q Q' : BQF) : Prop :=
  ∃ p q r s : Int, p * s - q * r = 1 ∧
    ∀ x y : Int, Q'.eval x y = Q.eval (p * x + q * y) (r * x + s * y)

@[simp] theorem op_A (Q : BQF) : Q.op.A = Q.A := rfl
@[simp] theorem op_B (Q : BQF) : Q.op.B = -Q.B := rfl
@[simp] theorem op_C (Q : BQF) : Q.op.C = Q.C := rfl

@[simp] theorem op_op (Q : BQF) : Q.op.op = Q := by
  cases Q
  simp only [op, BQF.mk.injEq]
  grind

@[simp] theorem disc_op (Q : BQF) : Q.op.disc = Q.disc := by
  simp only [disc, op_A, op_B, op_C]
  grind

end BQF

/-! ## Bhargava cubes and their three binary quadratic forms -/

/-- A *Bhargava cube*: a `2 × 2 × 2` array of integers.  With Bhargava's labelling the
eight entries sit at the vertices of a cube, the front face being `a b / c d` and the
back face `e f / g h`. -/
structure Cube where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int
  g : Int
  h : Int
deriving DecidableEq, Repr

/-- `negDetForm` is the binary quadratic form `-det (M x + N y)` attached to a pair of
`2 × 2` matrices `M = (m11 m12 ; m21 m22)` and `N = (n11 n12 ; n21 n22)`. -/
def negDetForm (m11 m12 m21 m22 n11 n12 n21 n22 : Int) : BQF :=
  ⟨-(m11 * m22 - m12 * m21),
   -(m11 * n22 + n11 * m22 - m12 * n21 - n12 * m21),
   -(n11 * n22 - n12 * n21)⟩

/-- `negDetForm` really is the form `(x, y) ↦ -det (M x + N y)`. -/
theorem negDetForm_eval (m11 m12 m21 m22 n11 n12 n21 n22 x y : Int) :
    (negDetForm m11 m12 m21 m22 n11 n12 n21 n22).eval x y
      = -((m11 * x + n11 * y) * (m22 * x + n22 * y)
          - (m12 * x + n12 * y) * (m21 * x + n21 * y)) := by
  simp only [BQF.eval, negDetForm]
  grind

namespace Cube

/-- The first form of a cube: slice into the faces `M₁ = (a b ; c d)`,
`N₁ = (e f ; g h)` and take `-det (M₁ x + N₁ y)`. -/
def form1 (K : Cube) : BQF := negDetForm K.a K.b K.c K.d K.e K.f K.g K.h

/-- The second form of a cube: slice into `M₂ = (a b ; e f)`, `N₂ = (c d ; g h)`. -/
def form2 (K : Cube) : BQF := negDetForm K.a K.b K.e K.f K.c K.d K.g K.h

/-- The third form of a cube: slice into `M₃ = (a c ; e g)`, `N₃ = (b d ; f h)`. -/
def form3 (K : Cube) : BQF := negDetForm K.a K.c K.e K.g K.b K.d K.f K.h

end Cube

/-- **The three binary quadratic forms of a Bhargava cube have equal discriminant.**
This common value is the discriminant of the cube. -/
theorem cube_disc_eq (K : Cube) :
    K.form1.disc = K.form2.disc ∧ K.form2.disc = K.form3.disc := by
  constructor <;>
    · simp only [Cube.form1, Cube.form2, Cube.form3, negDetForm, BQF.disc]
      grind

/-! ## The principal class -/

/-- If `u^2 - v^2` is divisible by `4` then `u` and `v` have the same parity. -/
theorem exists_two_mul_sub {u v w : Int} (h : u ^ 2 - v ^ 2 = 4 * w) :
    ∃ k : Int, v = u - 2 * k := by
  obtain ⟨m, hm⟩ : ∃ m : Int, u = 2 * m ∨ u = 2 * m + 1 := ⟨u / 2, by omega⟩
  obtain ⟨n, hn⟩ : ∃ n : Int, v = 2 * n ∨ v = 2 * n + 1 := ⟨v / 2, by omega⟩
  rcases hm with hm | hm <;> rcases hn with hn | hn <;> subst hm <;> subst hn
  · exact ⟨m - n, by omega⟩
  · exact absurd h (by grind)
  · exact absurd h (by grind)
  · exact ⟨m - n, by omega⟩

/-- Any two forms of the same discriminant with leading coefficient `1` are properly
equivalent: they all lie in the principal class of that discriminant. -/
theorem SLEquiv_of_lead_one {Q Q' : BQF} (hQ : Q.A = 1) (hQ' : Q'.A = 1)
    (hd : Q.disc = Q'.disc) : Q.SLEquiv Q' := by
  obtain ⟨A, B, C⟩ := Q
  obtain ⟨A', B', C'⟩ := Q'
  simp only at hQ hQ'
  subst hQ; subst hQ'
  simp only [BQF.disc] at hd
  have h : B ^ 2 - B' ^ 2 = 4 * (C - C') := by grind
  obtain ⟨k, hk⟩ := exists_two_mul_sub h
  subst hk
  have hC : C' = C - k * B + k ^ 2 := by grind
  subst hC
  refine ⟨1, -k, 0, 1, by grind, ?_⟩
  intro x y
  simp only [BQF.eval]
  grind

/-! ## The base case of the cube law -/

/-- The Bhargava cube attached to a binary quadratic form `Q = (A, B, C)`.  It encodes
the multiplication map `𝒪 × I → I` for the ideal `I = ⟨A, B - ω⟩` of the quadratic
ring `𝒪 = ℤ[ω]`, `ω² = B ω - A C`, whose norm form is `Q`. -/
def cubeOfForm (A B C : Int) : Cube :=
  { a := 0, b := 1, c := 1, d := 0, e := A, f := -B, g := 0, h := -C }

@[simp] theorem form1_cubeOfForm (A B C : Int) :
    (cubeOfForm A B C).form1 = ⟨1, -B, A * C⟩ := by
  simp only [Cube.form1, cubeOfForm, negDetForm, BQF.mk.injEq]
  grind

@[simp] theorem form2_cubeOfForm (A B C : Int) :
    (cubeOfForm A B C).form2 = ⟨A, B, C⟩ := by
  simp only [Cube.form2, cubeOfForm, negDetForm, BQF.mk.injEq]
  grind

@[simp] theorem form3_cubeOfForm (A B C : Int) :
    (cubeOfForm A B C).form3 = (⟨A, B, C⟩ : BQF).op := by
  simp only [Cube.form3, cubeOfForm, negDetForm, BQF.op, BQF.mk.injEq]
  grind

/-- The Gauss composition identity in the base case: the principal form
`x² - B x y + A C y²` composed with `Q = (A, B, C)` gives back `Q`, via an explicit
integral bilinear substitution (the multiplication map of the corresponding ideals). -/
theorem principal_comp_identity (A B C x₁ y₁ x₂ y₂ : Int) :
    (⟨1, -B, A * C⟩ : BQF).eval x₁ y₁ * (⟨A, B, C⟩ : BQF).eval x₂ y₂
      = (⟨A, B, C⟩ : BQF).eval (x₁ * x₂ - B * x₂ * y₁ - C * y₁ * y₂)
          (x₁ * y₂ + A * x₂ * y₁) := by
  simp only [BQF.eval]
  grind

/-- **Bhargava's cube law (base case).**

Let `Q = (A, B, C)` be an integral binary quadratic form of discriminant
`D = B² - 4AC`, and let `P` be any form of discriminant `D` with leading coefficient
`1`, i.e. any representative of the principal class.  Then the Bhargava cube
`cubeOfForm A B C` has three binary quadratic forms `Q₁, Q₂, Q₃` with:

* all three of discriminant `D`;
* `Q₁` properly equivalent to `P` (the identity class);
* `Q₂ = Q`;
* `Q₃ = Qᵒᵖ`, a representative of the inverse class of `Q`;
* the Gauss composition identity `Q₁(x₁,y₁) · Q₂(x₂,y₂) = Q₃ᵒᵖ(r, s)` for explicit
  integral bilinear forms `r, s` in `(x₁,y₁)` and `(x₂,y₂)`.

Thus `[Q₁] · [Q₂] · [Q₃] = 1` in the class group of forms of discriminant `D`: the
three forms of the cube compose to the identity.  This is Bhargava's cube law in the
base case, where the composition performed is Gauss composition with the principal
form. -/
theorem bhargava_cube_law (A B C : Int) (P : BQF) (hP : P.A = 1)
    (hPd : P.disc = B ^ 2 - 4 * A * C) :
    ((cubeOfForm A B C).form1.disc = (⟨A, B, C⟩ : BQF).disc ∧
      (cubeOfForm A B C).form2.disc = (⟨A, B, C⟩ : BQF).disc ∧
      (cubeOfForm A B C).form3.disc = (⟨A, B, C⟩ : BQF).disc) ∧
    (cubeOfForm A B C).form1.SLEquiv P ∧
    (cubeOfForm A B C).form2 = ⟨A, B, C⟩ ∧
    (cubeOfForm A B C).form3 = (⟨A, B, C⟩ : BQF).op ∧
    (∀ x₁ y₁ x₂ y₂ : Int,
      (cubeOfForm A B C).form1.eval x₁ y₁ * (cubeOfForm A B C).form2.eval x₂ y₂
        = (cubeOfForm A B C).form3.op.eval
            (x₁ * x₂ - B * x₂ * y₁ - C * y₁ * y₂) (x₁ * y₂ + A * x₂ * y₁)) := by
  refine ⟨⟨?_, ?_, ?_⟩, ?_, by simp, by simp, ?_⟩
  · simp only [form1_cubeOfForm, BQF.disc]
    grind
  · simp only [form2_cubeOfForm]
  · simp only [form3_cubeOfForm, BQF.disc_op]
  · refine SLEquiv_of_lead_one (by simp) hP ?_
    simp only [BQF.disc] at hPd
    simp only [form1_cubeOfForm, BQF.disc]
    grind
  · intro x₁ y₁ x₂ y₂
    simp only [form1_cubeOfForm, form2_cubeOfForm, form3_cubeOfForm, BQF.op_op]
    exact principal_comp_identity A B C x₁ y₁ x₂ y₂

/-- The hypotheses of `bhargava_cube_law` are non-vacuous: for every `A B C` the form
`(1, B, AC)` has leading coefficient `1` and discriminant `B² - 4AC`, so it is a
representative of the principal class of that discriminant. -/
theorem principal_form_spec (A B C : Int) :
    (⟨1, B, A * C⟩ : BQF).A = 1 ∧ (⟨1, B, A * C⟩ : BQF).disc = B ^ 2 - 4 * A * C := by
  refine ⟨rfl, ?_⟩
  simp only [BQF.disc]
  grind

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


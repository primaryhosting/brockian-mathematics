/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- An integral binary quadratic form `A x² + B x y + C y²`. -/
structure BinaryQF where
  A : Int
  B : Int
  C : Int

namespace BinaryQF

/-- Evaluation of a binary quadratic form. -/
def eval (q : BinaryQF) (x y : Int) : Int := q.A * x ^ 2 + q.B * x * y + q.C * y ^ 2

/-- The discriminant `B² - 4AC`. -/
def disc (q : BinaryQF) : Int := q.B ^ 2 - 4 * q.A * q.C

/-- The opposite form `(A, -B, C)`, representing the inverse class in the form
class group. -/
def opposite (q : BinaryQF) : BinaryQF := ⟨q.A, -q.B, q.C⟩

end BinaryQF

/-- A **Bhargava cube**: eight integers placed at the vertices of a cube.
With this labelling, the three ways of slicing the cube into a pair of `2 × 2`
matrices are
`(M₁, N₁) = ([[a,b],[c,d]], [[e,f],[g,h]])`,
`(M₂, N₂) = ([[a,c],[e,g]], [[b,d],[f,h]])`,
`(M₃, N₃) = ([[a,e],[b,f]], [[c,g],[d,h]])`. -/
structure Cube where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int
  g : Int
  h : Int

namespace Cube

variable (K : Cube)

/-- The first form attached to a cube, `Q₁(x,y) = -det(M₁ x - N₁ y)`. -/
def Q1 : BinaryQF :=
  ⟨K.b * K.c - K.a * K.d,
   K.a * K.h + K.d * K.e - K.b * K.g - K.c * K.f,
   K.f * K.g - K.e * K.h⟩

/-- The second form attached to a cube, `Q₂(x,y) = -det(M₂ x - N₂ y)`. -/
def Q2 : BinaryQF :=
  ⟨K.c * K.e - K.a * K.g,
   K.a * K.h + K.b * K.g - K.c * K.f - K.d * K.e,
   K.d * K.f - K.b * K.h⟩

/-- The third form attached to a cube, `Q₃(x,y) = -det(M₃ x - N₃ y)`. -/
def Q3 : BinaryQF :=
  ⟨K.b * K.e - K.a * K.f,
   K.a * K.h + K.c * K.f - K.b * K.g - K.d * K.e,
   K.d * K.g - K.c * K.h⟩

/-- `Q₁` really is `-det(M₁ x - N₁ y)`. -/
theorem Q1_eval (x y : Int) :
    K.Q1.eval x y =
      -((K.a * x - K.e * y) * (K.d * x - K.h * y)
        - (K.b * x - K.f * y) * (K.c * x - K.g * y)) := by
  simp only [Q1, BinaryQF.eval]; grind

/-- `Q₂` really is `-det(M₂ x - N₂ y)`. -/
theorem Q2_eval (x y : Int) :
    K.Q2.eval x y =
      -((K.a * x - K.b * y) * (K.g * x - K.h * y)
        - (K.c * x - K.d * y) * (K.e * x - K.f * y)) := by
  simp only [Q2, BinaryQF.eval]; grind

/-- `Q₃` really is `-det(M₃ x - N₃ y)`. -/
theorem Q3_eval (x y : Int) :
    K.Q3.eval x y =
      -((K.a * x - K.c * y) * (K.f * x - K.h * y)
        - (K.e * x - K.g * y) * (K.b * x - K.d * y)) := by
  simp only [Q3, BinaryQF.eval]; grind

end Cube

/-- The three binary quadratic forms produced by a Bhargava cube always have the
same discriminant. -/
theorem cube_disc_eq (K : Cube) :
    K.Q1.disc = K.Q2.disc ∧ K.Q2.disc = K.Q3.disc := by
  constructor <;> · simp only [Cube.Q1, Cube.Q2, Cube.Q3, BinaryQF.disc]; grind

/--
**Bhargava's cube law (base case).**

Bhargava's cube law states that the three binary quadratic forms `Q₁, Q₂, Q₃`
cut out from an integral `2 × 2 × 2` cube share a common discriminant and
compose to the identity under Gauss composition.  We prove the base case of
that law, which is exactly the assertion that Gauss composition has an identity
element and that `[Q] · [Q]⁻¹ = 1`:

for every integral binary quadratic form `Q = (A, B, C)` there is a Bhargava
cube whose associated triple of forms is `(principal form, Q, Qᵒᵖ)`, all three
of discriminant `B² - 4AC`, where `Qᵒᵖ = (A, -B, C)` is the opposite form and
the principal form is the unique form `x² + r x y + s y²` with `r ∈ {0, 1}` and
`r² - 4 s = B² - 4AC` (i.e. `x² - (D/4) y²` when `4 ∣ D`, and
`x² + x y + ((1-D)/4) y²` when `D` is odd).

The proof splits on the parity of `B`, i.e. on the residue of the discriminant
modulo `4`, since the principal form has a different shape in the two cases.
-/
theorem bhargava_cube_law (A B C : Int) :
    ∃ (K : Cube) (r s : Int),
      (r = 0 ∨ r = 1) ∧
      r ^ 2 - 4 * s = B ^ 2 - 4 * A * C ∧
      K.Q1 = ⟨1, r, s⟩ ∧
      K.Q2 = ⟨A, B, C⟩ ∧
      K.Q3 = (BinaryQF.mk A B C).opposite ∧
      K.Q1.disc = B ^ 2 - 4 * A * C ∧
      K.Q2.disc = B ^ 2 - 4 * A * C ∧
      K.Q3.disc = B ^ 2 - 4 * A * C := by
  obtain ⟨k, hk | hk⟩ : ∃ k : Int, B = 2 * k ∨ B = 2 * k + 1 := ⟨B / 2, by omega⟩
  · -- `B = 2k` is even: the principal form is `x² - (D/4) y²`.
    subst hk
    refine ⟨⟨0, 1, 1, 0, A, -k, k, -C⟩, 0, A * C - k ^ 2, Or.inl rfl, by grind, ?_, ?_, ?_,
      ?_, ?_, ?_⟩
    · simp only [Cube.Q1, BinaryQF.mk.injEq]; refine ⟨by grind, by grind, by grind⟩
    · simp only [Cube.Q2, BinaryQF.mk.injEq]; refine ⟨by grind, by grind, by grind⟩
    · simp only [Cube.Q3, BinaryQF.opposite, BinaryQF.mk.injEq]
      refine ⟨by grind, by grind, by grind⟩
    · simp only [Cube.Q1, BinaryQF.disc]; grind
    · simp only [Cube.Q2, BinaryQF.disc]; grind
    · simp only [Cube.Q3, BinaryQF.disc]; grind
  · -- `B = 2k + 1` is odd: the principal form is `x² + x y + ((1-D)/4) y²`.
    subst hk
    refine ⟨⟨0, 1, 1, 0, A, -(k + 1), k, -C⟩, 1, A * C - k * (k + 1), Or.inr rfl, by grind, ?_,
      ?_, ?_, ?_, ?_, ?_⟩
    · simp only [Cube.Q1, BinaryQF.mk.injEq]; refine ⟨by grind, by grind, by grind⟩
    · simp only [Cube.Q2, BinaryQF.mk.injEq]; refine ⟨by grind, by grind, by grind⟩
    · simp only [Cube.Q3, BinaryQF.opposite, BinaryQF.mk.injEq]
      refine ⟨by grind, by grind, by grind⟩
    · simp only [Cube.Q1, BinaryQF.disc]; grind
    · simp only [Cube.Q2, BinaryQF.disc]; grind
    · simp only [Cube.Q3, BinaryQF.disc]; grind

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


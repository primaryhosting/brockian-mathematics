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

/-! ## Integral binary quadratic forms -/

/-- An integral binary quadratic form `A x² + B x y + C y²`, recorded by its coefficients. -/
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
def eval (Q : BQF) (x y : ℤ) : ℤ := Q.A * x ^ 2 + Q.B * x * y + Q.C * y ^ 2

/-- The discriminant `B² - 4AC`. -/
def disc (Q : BQF) : ℤ := Q.B ^ 2 - 4 * Q.A * Q.C

/-- The opposite (inverse) form `A x² - B x y + C y²`; it represents the inverse class
in the form class group. -/
def opp (Q : BQF) : BQF := ⟨Q.A, -Q.B, Q.C⟩

@[simp] lemma opp_A (Q : BQF) : Q.opp.A = Q.A := rfl
@[simp] lemma opp_B (Q : BQF) : Q.opp.B = -Q.B := rfl
@[simp] lemma opp_C (Q : BQF) : Q.opp.C = Q.C := rfl

@[simp] lemma disc_opp (Q : BQF) : Q.opp.disc = Q.disc := by
  simp [disc, opp]

end BQF

/-! ## Bhargava cubes -/

/-- A *Bhargava cube*: eight integers placed at the vertices of a cube.  The names record
the vertex coordinates: `a = 000`, `b = 100`, `c = 010`, `d = 110`, `e = 001`, `f = 101`,
`g = 011`, `h = 111`. -/
structure Cube where
  /-- vertex `000` -/
  a : ℤ
  /-- vertex `100` -/
  b : ℤ
  /-- vertex `010` -/
  c : ℤ
  /-- vertex `110` -/
  d : ℤ
  /-- vertex `001` -/
  e : ℤ
  /-- vertex `101` -/
  f : ℤ
  /-- vertex `011` -/
  g : ℤ
  /-- vertex `111` -/
  h : ℤ
  deriving DecidableEq

namespace Cube

/-- First pair of opposite faces: `M₁ = ![![a, b], ![c, d]]`. -/
def M1 (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.b; K.c, K.d]
/-- First pair of opposite faces: `N₁ = ![![e, f], ![g, h]]`. -/
def N1 (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.e, K.f; K.g, K.h]
/-- Second pair of opposite faces: `M₂ = ![![a, c], ![e, g]]`. -/
def M2 (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.c; K.e, K.g]
/-- Second pair of opposite faces: `N₂ = ![![b, d], ![f, h]]`. -/
def N2 (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.b, K.d; K.f, K.h]
/-- Third pair of opposite faces: `M₃ = ![![a, e], ![b, f]]`. -/
def M3 (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.a, K.e; K.b, K.f]
/-- Third pair of opposite faces: `N₃ = ![![c, g], ![d, h]]`. -/
def N3 (K : Cube) : Matrix (Fin 2) (Fin 2) ℤ := !![K.c, K.g; K.d, K.h]

/-- The first quadratic form attached to a cube. -/
def Q1 (K : Cube) : BQF :=
  ⟨K.b * K.c - K.a * K.d,
   K.b * K.g + K.c * K.f - K.a * K.h - K.d * K.e,
   K.f * K.g - K.e * K.h⟩

/-- The second quadratic form attached to a cube. -/
def Q2 (K : Cube) : BQF :=
  ⟨K.c * K.e - K.a * K.g,
   K.c * K.f + K.d * K.e - K.a * K.h - K.b * K.g,
   K.d * K.f - K.b * K.h⟩

/-- The third quadratic form attached to a cube. -/
def Q3 (K : Cube) : BQF :=
  ⟨K.b * K.e - K.a * K.f,
   K.d * K.e + K.b * K.g - K.a * K.h - K.c * K.f,
   K.d * K.g - K.c * K.h⟩

/-- `Q₁` is `-det(M₁ x + N₁ y)`, as in Bhargava's definition. -/
lemma Q1_eval (K : Cube) (x y : ℤ) :
    (K.Q1).eval x y = -((K.M1.map (fun t => t * x) + K.N1.map (fun t => t * y)).det) := by
  simp [Q1, BQF.eval, M1, N1, Matrix.det_fin_two, Matrix.map]
  ring

/-- `Q₂` is `-det(M₂ x + N₂ y)`. -/
lemma Q2_eval (K : Cube) (x y : ℤ) :
    (K.Q2).eval x y = -((K.M2.map (fun t => t * x) + K.N2.map (fun t => t * y)).det) := by
  simp [Q2, BQF.eval, M2, N2, Matrix.det_fin_two, Matrix.map]
  ring

/-- `Q₃` is `-det(M₃ x + N₃ y)`. -/
lemma Q3_eval (K : Cube) (x y : ℤ) :
    (K.Q3).eval x y = -((K.M3.map (fun t => t * x) + K.N3.map (fun t => t * y)).det) := by
  simp [Q3, BQF.eval, M3, N3, Matrix.det_fin_two, Matrix.map]
  ring

/-- The three forms of a cube all have the same discriminant. -/
theorem disc_Q1_eq_disc_Q2 (K : Cube) : (K.Q1).disc = (K.Q2).disc := by
  simp only [BQF.disc, Q1, Q2]
  ring

/-- The three forms of a cube all have the same discriminant. -/
theorem disc_Q2_eq_disc_Q3 (K : Cube) : (K.Q2).disc = (K.Q3).disc := by
  simp only [BQF.disc, Q2, Q3]
  ring

/-- The common discriminant of the three forms of a cube. -/
theorem disc_Q1_eq_disc_Q3 (K : Cube) : (K.Q1).disc = (K.Q3).disc :=
  (disc_Q1_eq_disc_Q2 K).trans (disc_Q2_eq_disc_Q3 K)

end Cube

/-! ## Concordant forms and Gauss (Dirichlet) composition -/

/-- The *concordant cube* attached to data `(a₁, a₂, b, c)`.  Its three quadratic forms are
`(a₁, b, a₂c)`, `(a₂, b, a₁c)` and the opposite of their Gauss composite `(a₁a₂, b, c)`. -/
def concordantCube (a1 a2 b c : ℤ) : Cube :=
  { a := 0, b := a1, c := 1, d := 0, e := a2, f := b, g := 0, h := -c }

/-- Gauss (Dirichlet) composite of the two concordant forms `(a₁, b, a₂c)` and `(a₂, b, a₁c)`. -/
def gaussCompose (a1 a2 b c : ℤ) : BQF := ⟨a1 * a2, b, c⟩

/-- First bilinear form occurring in Gauss composition. -/
def composeX (c : ℤ) (x1 y1 x2 y2 : ℤ) : ℤ := x1 * x2 - c * (y1 * y2)

/-- Second bilinear form occurring in Gauss composition. -/
def composeY (a1 a2 b : ℤ) (x1 y1 x2 y2 : ℤ) : ℤ :=
  a1 * (x1 * y2) + a2 * (x2 * y1) + b * (y1 * y2)

/-! ## The cube law -/

/--
**Bhargava's cube law (base case).**

For the concordant cube `K = concordantCube a₁ a₂ b c` attached to arbitrary integers
`a₁, a₂, b, c`:

* its three quadratic forms are exactly `Q₁ = (a₁, b, a₂c)`, `Q₂ = (a₂, b, a₁c)` and
  `Q₃ = (a₁a₂, -b, c)`, the last being the *opposite* (i.e. class-group inverse) of the
  Gauss composite `Q₁ ∘ Q₂ = (a₁a₂, b, c)`;
* all three forms have the same discriminant `b² - 4a₁a₂c` (this holds for *every* cube,
  see `Frontier.Cube.disc_Q1_eq_disc_Q2`);
* the classical Gauss/Dirichlet composition identity holds:
  `Q₁(x₁,y₁) · Q₂(x₂,y₂) = (Q₁ ∘ Q₂)(X, Y)` with `X, Y` the explicit bilinear forms
  `composeX`, `composeY`.

Together these say that `Q₁ · Q₂ · Q₃ = 1` in the class group of forms of discriminant
`b² - 4a₁a₂c`, i.e. the cube law recovers Gauss composition.
-/
theorem bhargava_cube_law (a1 a2 b c : ℤ) :
    let K : Cube := concordantCube a1 a2 b c
    K.Q1 = ⟨a1, b, a2 * c⟩ ∧
    K.Q2 = ⟨a2, b, a1 * c⟩ ∧
    K.Q3 = (gaussCompose a1 a2 b c).opp ∧
    (K.Q1).disc = b ^ 2 - 4 * (a1 * a2) * c ∧
    (K.Q2).disc = b ^ 2 - 4 * (a1 * a2) * c ∧
    (K.Q3).disc = b ^ 2 - 4 * (a1 * a2) * c ∧
    (∀ x1 y1 x2 y2 : ℤ,
      (K.Q1).eval x1 y1 * (K.Q2).eval x2 y2 =
        (gaussCompose a1 a2 b c).eval
          (composeX c x1 y1 x2 y2) (composeY a1 a2 b x1 y1 x2 y2)) := by
  intro K
  have hQ1 : K.Q1 = ⟨a1, b, a2 * c⟩ := by
    simp only [K, Cube.Q1, concordantCube, BQF.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  have hQ2 : K.Q2 = ⟨a2, b, a1 * c⟩ := by
    simp only [K, Cube.Q2, concordantCube, BQF.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  have hQ3 : K.Q3 = (gaussCompose a1 a2 b c).opp := by
    simp only [K, Cube.Q3, concordantCube, gaussCompose, BQF.opp, BQF.mk.injEq]
    refine ⟨by ring, by ring, by ring⟩
  refine ⟨hQ1, hQ2, hQ3, ?_, ?_, ?_, ?_⟩
  · rw [hQ1]; simp only [BQF.disc]; ring
  · rw [hQ2]; simp only [BQF.disc]; ring
  · rw [hQ3]; simp only [BQF.disc, BQF.opp, gaussCompose]; ring
  · intro x1 y1 x2 y2
    rw [hQ1, hQ2]
    simp only [BQF.eval, gaussCompose, composeX, composeY]
    ring

end Frontier


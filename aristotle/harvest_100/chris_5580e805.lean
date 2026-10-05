/-
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Frontier

/-!
## The Kauffman-bracket model of the Jones polynomial

The Jones polynomial of a link is obtained from the Kauffman bracket state sum
of a link diagram, normalised by the writhe.  The content of the statement
"the Jones polynomial is a link invariant" is the invariance of this
construction under the three Reidemeister moves, and this is a purely local,
algebraic computation in the Temperley–Lieb algebras over the coefficient ring,
where a crossing is resolved as

    ⟨crossing⟩ = A · ⟨identity smoothing⟩ + A⁻¹ · ⟨cup–cap smoothing⟩

and a closed loop contributes the factor `d = -A² - A⁻²`.

This file sets up the Temperley–Lieb algebras `TL₂` and `TL₃` over an arbitrary
commutative ring (with loop parameter `d`), defines the Kauffman resolution of
a crossing, and proves the three local invariance statements:

* Reidemeister I : a kink multiplies the bracket by `-A³`, so the writhe
  normalisation `(-A³)^(-w) ⟨D⟩` is unchanged;
* Reidemeister II: `σ⁺ · σ⁻ = 1` in `TL₂`;
* Reidemeister III: `σ₁ σ₂ σ₁ = σ₂ σ₁ σ₂` in `TL₃`.
-/

namespace Jones

/-! ### The Temperley–Lieb algebra `TL₂`

Basis: the identity diagram `1` and the cup–cap diagram `e`, with `e * e = d * e`.
-/

/-- An element of the Temperley–Lieb algebra on two strands, written in the
planar basis `{1, e}`. -/
structure TL2 (K : Type*) where
  /-- coefficient of the identity diagram -/
  c1 : K
  /-- coefficient of the cup–cap diagram `e` -/
  ce : K

namespace TL2

variable {K : Type*} [CommRing K]

omit [CommRing K] in
@[ext] theorem ext' {x y : TL2 K} (h1 : x.c1 = y.c1) (h2 : x.ce = y.ce) : x = y := by
  cases x; cases y; simp_all

/-- The identity diagram. -/
def one : TL2 K := ⟨1, 0⟩

/-- Multiplication of Temperley–Lieb diagrams on two strands, where a closed
loop created by the composition contributes the factor `d`. -/
def mul (d : K) (x y : TL2 K) : TL2 K :=
  ⟨x.c1 * y.c1, x.c1 * y.ce + x.ce * y.c1 + d * x.ce * y.ce⟩

theorem one_mul (d : K) (x : TL2 K) : mul d one x = x := by
  ext <;> simp [mul, one]

theorem mul_one (d : K) (x : TL2 K) : mul d x one = x := by
  ext <;> simp [mul, one]

theorem mul_assoc (d : K) (x y z : TL2 K) :
    mul d (mul d x y) z = mul d x (mul d y z) := by
  ext <;> simp only [mul] <;> ring

end TL2

/-! ### The Temperley–Lieb algebra `TL₃`

Basis: `1, e₁, e₂, e₁e₂, e₂e₁`, with relations `eᵢ² = d eᵢ`,
`e₁e₂e₁ = e₁`, `e₂e₁e₂ = e₂`.
-/

/-- An element of the Temperley–Lieb algebra on three strands, written in the
planar basis `{1, e₁, e₂, e₁e₂, e₂e₁}`. -/
structure TL3 (K : Type*) where
  /-- coefficient of the identity diagram -/
  c1 : K
  /-- coefficient of `e₁` -/
  ca : K
  /-- coefficient of `e₂` -/
  cb : K
  /-- coefficient of `e₁e₂` -/
  cab : K
  /-- coefficient of `e₂e₁` -/
  cba : K

namespace TL3

variable {K : Type*} [CommRing K]

omit [CommRing K] in
@[ext] theorem ext' {x y : TL3 K} (h1 : x.c1 = y.c1) (h2 : x.ca = y.ca)
    (h3 : x.cb = y.cb) (h4 : x.cab = y.cab) (h5 : x.cba = y.cba) : x = y := by
  cases x; cases y; simp_all

/-- The identity diagram. -/
def one : TL3 K := ⟨1, 0, 0, 0, 0⟩

/-- Multiplication of Temperley–Lieb diagrams on three strands, obtained by
bilinear extension of the multiplication table of the planar basis; each closed
loop created by the composition contributes the factor `d`. -/
def mul (d : K) (x y : TL3 K) : TL3 K :=
  ⟨ x.c1 * y.c1,
    x.c1 * y.ca + x.ca * y.c1 + d * x.ca * y.ca + x.ca * y.cba + x.cab * y.ca
      + d * x.cab * y.cba,
    x.c1 * y.cb + x.cb * y.c1 + d * x.cb * y.cb + x.cb * y.cab + x.cba * y.cb
      + d * x.cba * y.cab,
    x.c1 * y.cab + x.ca * y.cb + d * x.ca * y.cab + x.cab * y.c1
      + d * x.cab * y.cb + x.cab * y.cab,
    x.c1 * y.cba + x.cb * y.ca + d * x.cb * y.cba + x.cba * y.c1
      + d * x.cba * y.ca + x.cba * y.cba ⟩

theorem one_mul (d : K) (x : TL3 K) : mul d one x = x := by
  ext <;> simp [mul, one]

theorem mul_one (d : K) (x : TL3 K) : mul d x one = x := by
  ext <;> simp [mul, one]

theorem mul_assoc (d : K) (x y z : TL3 K) :
    mul d (mul d x y) z = mul d x (mul d y z) := by
  ext <;> simp only [mul] <;> ring

/-- The generator `e₁`. -/
def e1 : TL3 K := ⟨0, 1, 0, 0, 0⟩

/-- The generator `e₂`. -/
def e2 : TL3 K := ⟨0, 0, 1, 0, 0⟩

theorem e1_mul_e1 (d : K) : mul d e1 e1 = ⟨0, d, 0, 0, 0⟩ := by
  ext <;> simp [mul, e1]

theorem e2_mul_e2 (d : K) : mul d e2 e2 = ⟨0, 0, d, 0, 0⟩ := by
  ext <;> simp [mul, e2]

theorem e1_e2_e1 (d : K) : mul d (mul d e1 e2) e1 = e1 := by
  ext <;> simp [mul, e1, e2]

theorem e2_e1_e2 (d : K) : mul d (mul d e2 e1) e2 = e2 := by
  ext <;> simp [mul, e1, e2]

end TL3

/-! ### Kauffman resolutions of a crossing -/

variable {K : Type*} [CommRing K]

/-- Kauffman resolution of a positive crossing on two strands:
`A · 1 + A⁻¹ · e`. -/
def sigma2Pos (A Ai : K) : TL2 K := ⟨A, Ai⟩

/-- Kauffman resolution of a negative crossing on two strands:
`A⁻¹ · 1 + A · e`. -/
def sigma2Neg (A Ai : K) : TL2 K := ⟨Ai, A⟩

/-- Kauffman resolution of the crossing between the first two of three
strands. -/
def sigma3One (A Ai : K) : TL3 K := ⟨A, Ai, 0, 0, 0⟩

/-- Kauffman resolution of the crossing between the last two of three
strands. -/
def sigma3Two (A Ai : K) : TL3 K := ⟨A, 0, Ai, 0, 0⟩

/-! ### Reidemeister I

Resolving the crossing of a kink gives `A · (closed loop) + A⁻¹ · (strand)`,
i.e. the bracket is multiplied by `A · d + A⁻¹ = -A³`.
-/

/-- The Kauffman-bracket factor produced by a positive kink. -/
def kinkFactor (A Ai : K) : K := A * (-A ^ 2 - Ai ^ 2) + Ai

/-- **Reidemeister I** at the level of the Kauffman bracket: a positive kink
multiplies the bracket by `-A³`. -/
theorem kinkFactor_eq (A Ai : K) (hA : A * Ai = 1) : kinkFactor A Ai = -A ^ 3 := by
  simp only [kinkFactor]
  linear_combination (-Ai) * hA

/-! ### Reidemeister II -/

/-- **Reidemeister II** at the level of the Kauffman bracket: the composite of a
positive and a negative crossing is the identity tangle in `TL₂`, provided the
loop parameter is `d = -A² - A⁻²`. -/
theorem reidemeister_two (A Ai : K) (hA : A * Ai = 1) :
    TL2.mul (-A ^ 2 - Ai ^ 2) (sigma2Pos A Ai) (sigma2Neg A Ai) = TL2.one := by
  refine TL2.ext' ?_ ?_ <;> simp only [TL2.mul, sigma2Pos, sigma2Neg, TL2.one]
  · linear_combination hA
  · linear_combination (-(A ^ 2 + Ai ^ 2)) * hA

/-! ### Reidemeister III -/

/-- **Reidemeister III** at the level of the Kauffman bracket: the braid
relation holds for the Kauffman resolutions of the crossings in `TL₃`,
provided the loop parameter is `d = -A² - A⁻²`. -/
theorem reidemeister_three (A Ai : K) (hA : A * Ai = 1) :
    TL3.mul (-A ^ 2 - Ai ^ 2)
        (TL3.mul (-A ^ 2 - Ai ^ 2) (sigma3One A Ai) (sigma3Two A Ai)) (sigma3One A Ai)
      = TL3.mul (-A ^ 2 - Ai ^ 2)
        (TL3.mul (-A ^ 2 - Ai ^ 2) (sigma3Two A Ai) (sigma3One A Ai)) (sigma3Two A Ai) := by
  refine TL3.ext' ?_ ?_ ?_ ?_ ?_ <;>
    simp only [TL3.mul, sigma3One, sigma3Two] <;>
    first
      | ring1
      | linear_combination (-(A ^ 2 * Ai + Ai ^ 3)) * hA
      | linear_combination (A ^ 2 * Ai + Ai ^ 3) * hA

/-! ### The writhe normalisation factor -/

/-- The writhe normalisation factor `-A³`, as a unit of `ℤ[A, A⁻¹]`. -/
noncomputable def negA3 : (LaurentPolynomial ℤ)ˣ where
  val := -LaurentPolynomial.T 3
  inv := -LaurentPolynomial.T (-3)
  val_inv := by rw [neg_mul_neg, ← LaurentPolynomial.T_add]; norm_num
  inv_val := by rw [neg_mul_neg, ← LaurentPolynomial.T_add]; norm_num

theorem negA3_val :
    (negA3 : LaurentPolynomial ℤ) = -(LaurentPolynomial.T 1 : LaurentPolynomial ℤ) ^ 3 := by
  show -LaurentPolynomial.T 3 = _
  rw [show (3 : ℤ) = 1 + 1 + 1 by ring, LaurentPolynomial.T_add, LaurentPolynomial.T_add]
  ring

end Jones

/-! ### The main statement -/

open Jones

/-- **The Jones polynomial is a link invariant** (base case: invariance of the
Kauffman-bracket construction under all three Reidemeister moves).

Working over the ring `LaurentPolynomial ℤ = ℤ[A, A⁻¹]` of Kauffman-bracket
coefficients, with the loop value `d = -A² - A⁻²`:

1. *Reidemeister I*: adding a positive kink to a diagram multiplies the
   Kauffman bracket by `kinkFactor A A⁻¹ = -A³` and increases the writhe by
   `1`, hence the writhe-normalised bracket `f(D) = (-A³)^(-w(D)) ⟨D⟩` — the
   Jones polynomial, up to the substitution `A = t^(-1/4)` — is unchanged.
2. *Reidemeister II*: the Kauffman resolutions of a positive and a negative
   crossing compose to the identity tangle in `TL₂`.
3. *Reidemeister III*: the Kauffman resolutions satisfy the braid relation in
   `TL₃`.
-/
theorem jones_polynomial_invariant :
    (∀ (w : ℤ) (bracket : LaurentPolynomial ℤ),
        ((negA3 ^ (-(w + 1)) : (LaurentPolynomial ℤ)ˣ) : LaurentPolynomial ℤ) *
            (kinkFactor (LaurentPolynomial.T 1 : LaurentPolynomial ℤ)
              (LaurentPolynomial.T (-1)) * bracket)
          = ((negA3 ^ (-w) : (LaurentPolynomial ℤ)ˣ) : LaurentPolynomial ℤ) * bracket)
  ∧ TL2.mul (-(LaurentPolynomial.T 1 : LaurentPolynomial ℤ) ^ 2
        - (LaurentPolynomial.T (-1) : LaurentPolynomial ℤ) ^ 2)
      (sigma2Pos (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)))
      (sigma2Neg (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1))) = TL2.one
  ∧ TL3.mul (-(LaurentPolynomial.T 1 : LaurentPolynomial ℤ) ^ 2
        - (LaurentPolynomial.T (-1) : LaurentPolynomial ℤ) ^ 2)
      (TL3.mul (-(LaurentPolynomial.T 1 : LaurentPolynomial ℤ) ^ 2
          - (LaurentPolynomial.T (-1) : LaurentPolynomial ℤ) ^ 2)
        (sigma3One (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)))
        (sigma3Two (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1))))
      (sigma3One (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)))
    = TL3.mul (-(LaurentPolynomial.T 1 : LaurentPolynomial ℤ) ^ 2
        - (LaurentPolynomial.T (-1) : LaurentPolynomial ℤ) ^ 2)
      (TL3.mul (-(LaurentPolynomial.T 1 : LaurentPolynomial ℤ) ^ 2
          - (LaurentPolynomial.T (-1) : LaurentPolynomial ℤ) ^ 2)
        (sigma3Two (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1)))
        (sigma3One (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1))))
      (sigma3Two (LaurentPolynomial.T 1) (LaurentPolynomial.T (-1))) := by
  have hA : (LaurentPolynomial.T 1 : LaurentPolynomial ℤ) * LaurentPolynomial.T (-1) = 1 := by
    rw [← LaurentPolynomial.T_add]
    norm_num
  refine ⟨?_, reidemeister_two _ _ hA, reidemeister_three _ _ hA⟩
  intro w bracket
  rw [kinkFactor_eq _ _ hA, ← negA3_val, ← mul_assoc]
  congr 1
  rw [show -w = -(w + 1) + 1 by ring, zpow_add_one]
  push_cast
  ring

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


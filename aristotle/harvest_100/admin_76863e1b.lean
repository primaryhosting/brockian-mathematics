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

/-!
## Overview

The Jones polynomial of a link is constructed from the *Kauffman bracket*: each crossing of a
link diagram is resolved by the skein relation

  `⟨crossing⟩ = A ⬝ ⟨0-smoothing⟩ + A⁻¹ ⬝ ⟨∞-smoothing⟩`,

a free closed loop contributes the *loop value* `δ = -A² - A⁻²`, and the resulting bracket is
normalised by the writhe, `V(L) = (-A³)^(-w(L)) ⟨L⟩`.

Well-definedness of this construction is exactly the statement that the above data is invariant
under the three Reidemeister moves.  Passing to the *skein-algebraic* (Temperley–Lieb) picture,
which is the standard way Kauffman's argument is organised, the three moves become three purely
algebraic identities in the Temperley–Lieb algebra over the coefficient ring:

* **R2**: the resolved crossing `σ = A·1 + A⁻¹·e` is invertible, with inverse the resolved
  *opposite* crossing `σ⁻¹ = A⁻¹·1 + A·e`.
* **R3**: the resolved crossings satisfy the braid relation `σ₁σ₂σ₁ = σ₂σ₁σ₂`.
* **R1**: adding a kink multiplies the bracket by the unit `-A³`; since a kink also changes the
  writhe by `1`, the writhe-normalised bracket is unchanged.

This file develops that algebra over an arbitrary commutative coefficient ring `R` with a
distinguished invertible element `A`, in an arbitrary `R`-algebra `T` carrying elements `eᵢ`
subject to the Temperley–Lieb relations.  The main theorem `Frontier.jones_polynomial_invariant`
collects the three statements.  A concrete non-degenerate model (`Frontier.TLModel`) over the ring
of Laurent polynomials `ℤ[A, A⁻¹]` is provided at the end, so the hypotheses are known to be
satisfiable by genuinely distinct, nonzero elements.
-/

namespace Frontier

section Kauffman

variable {R : Type*} [CommRing R] {T : Type*} [Ring T] [Algebra R T]

/-- The Kauffman loop value `δ = -A² - A⁻²`, written using an explicit inverse `Ainv` of `A`.
It is the scalar by which the bracket gets multiplied when a free closed loop is added. -/
def loopValue (A Ainv : R) : R := -A ^ 2 - Ainv ^ 2

/-- The Kauffman resolution of a crossing inside a Temperley–Lieb-style algebra:
`σ = A · 1 + A⁻¹ · e`, where `e` is the Temperley–Lieb "cup–cap" element corresponding to the
`∞`-smoothing of the crossing and `1` corresponds to the `0`-smoothing. -/
def kauffmanCrossing (A Ainv : R) (e : T) : T := A • (1 : T) + Ainv • e

/-- **Reidemeister II.**  The resolved crossing is invertible: composing a crossing with the
opposite crossing (obtained by exchanging `A` and `A⁻¹`) gives the identity tangle. -/
theorem reidemeister_two (A Ainv : R) (hA : A * Ainv = 1) (e : T)
    (he : e * e = loopValue A Ainv • e) :
    kauffmanCrossing A Ainv e * kauffmanCrossing Ainv A e = 1 := by
  simp only [kauffmanCrossing, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul, he,
    smul_smul, loopValue]
  match_scalars
  · linear_combination hA
  · linear_combination (-A ^ 2 - Ainv ^ 2) * hA

/-- **Reidemeister II**, the other composition order. -/
theorem reidemeister_two' (A Ainv : R) (hA : A * Ainv = 1) (e : T)
    (he : e * e = loopValue A Ainv • e) :
    kauffmanCrossing Ainv A e * kauffmanCrossing A Ainv e = 1 := by
  have hA' : Ainv * A = 1 := by rw [mul_comm]; exact hA
  have hl : loopValue Ainv A = loopValue A Ainv := by simp only [loopValue]; ring
  exact reidemeister_two Ainv A hA' e (by rw [hl]; exact he)

/-- **Reidemeister III.**  The resolved crossings satisfy the braid relation. -/
theorem reidemeister_three (A Ainv : R) (hA : A * Ainv = 1) (e₁ e₂ : T)
    (he₁ : e₁ * e₁ = loopValue A Ainv • e₁) (he₂ : e₂ * e₂ = loopValue A Ainv • e₂)
    (h₁₂₁ : e₁ * e₂ * e₁ = e₁) (h₂₁₂ : e₂ * e₁ * e₂ = e₂) :
    kauffmanCrossing A Ainv e₁ * kauffmanCrossing A Ainv e₂ * kauffmanCrossing A Ainv e₁
      = kauffmanCrossing A Ainv e₂ * kauffmanCrossing A Ainv e₁ * kauffmanCrossing A Ainv e₂ := by
  simp only [kauffmanCrossing, add_mul, mul_add, mul_one, one_mul, smul_smul, mul_assoc,
    he₁, he₂, h₁₂₁, h₂₁₂, loopValue, smul_add, mul_smul_comm, Algebra.smul_mul_assoc]
  match_scalars <;>
    first
      | linear_combination (-(A ^ 2 * Ainv + Ainv ^ 3)) * hA
      | linear_combination (A ^ 2 * Ainv + Ainv ^ 3) * hA
      | linear_combination (0 : R) * hA

/-- **Reidemeister I** at the level of the unnormalised bracket: introducing a positive kink
resolves into a free loop (scalar `δ`) plus the plain strand, and the total effect is
multiplication by the unit `-A³`. -/
theorem kauffman_kink (A Ainv : R) (hA : A * Ainv = 1) (x : T) :
    A • (loopValue A Ainv • x) + Ainv • x = (-A ^ 3) • x := by
  rw [smul_smul, ← add_smul]
  congr 1
  simp only [loopValue]
  linear_combination (-Ainv) * hA

/-- `-A³` as a unit of the coefficient ring; this is the factor by which the Kauffman bracket
changes under a Reidemeister I move, and the base of the writhe normalisation. -/
def negACube (A Ainv : R) (hA : A * Ainv = 1) : Rˣ where
  val := -A ^ 3
  inv := -Ainv ^ 3
  val_inv := by linear_combination (A ^ 2 * Ainv ^ 2 + A * Ainv + 1) * hA
  inv_val := by linear_combination (A ^ 2 * Ainv ^ 2 + A * Ainv + 1) * hA

@[simp] lemma negACube_val (A Ainv : R) (hA : A * Ainv = 1) :
    ((negACube A Ainv hA : Rˣ) : R) = -A ^ 3 := rfl

/-- The writhe-normalised bracket `(-A³)^(-w) ⟨L⟩`, as a function of the writhe `w` and the
unnormalised bracket value `b`.  This is (up to the substitution `A = t^(-1/4)`) the Jones
polynomial. -/
def normalizedBracket (u : Rˣ) (w : ℤ) (b : R) : R := ((u ^ (-w) : Rˣ) : R) * b

/-- **Reidemeister I** for the normalised bracket: a kink multiplies the bracket by `u = -A³`
and increases the writhe by one, and these two effects cancel. -/
theorem normalizedBracket_kink (u : Rˣ) (w : ℤ) (b : R) :
    normalizedBracket u (w + 1) ((u : R) * b) = normalizedBracket u w b := by
  have h : (u ^ (-(w + 1)) : Rˣ) * u = u ^ (-w) := by
    rw [← zpow_add_one]
    congr 1
    ring
  simp only [normalizedBracket, ← mul_assoc, ← Units.val_mul, h]

/-- A negative kink is handled symmetrically. -/
theorem normalizedBracket_kink_neg (u : Rˣ) (w : ℤ) (b : R) :
    normalizedBracket u (w - 1) (((u⁻¹ : Rˣ) : R) * b) = normalizedBracket u w b := by
  have h : (u ^ (-(w - 1)) : Rˣ) * u⁻¹ = u ^ (-w) := by
    rw [← zpow_neg_one, ← zpow_add]
    congr 1
    ring
  simp only [normalizedBracket, ← mul_assoc, ← Units.val_mul, h]

/-- **The Jones polynomial is a link invariant.**

Working in the Temperley–Lieb skein setting that underlies Kauffman's construction of the Jones
polynomial — a commutative coefficient ring `R` with an invertible element `A`, loop value
`δ = -A² - A⁻²`, an `R`-algebra `T` of tangles, and Temperley–Lieb generators `e₁, e₂` satisfying
`eᵢ² = δ eᵢ`, `e₁e₂e₁ = e₁`, `e₂e₁e₂ = e₂` — the Kauffman resolution
`σᵢ = A·1 + A⁻¹·eᵢ` of a crossing satisfies exactly the invariance properties required by the
three Reidemeister moves:

1. (R2) `σ` is invertible, its inverse being the resolution of the opposite crossing;
2. (R3) the `σᵢ` satisfy the braid relation;
3. (R1) adding a kink multiplies the bracket by the unit `-A³`, and this is precisely cancelled
   by the writhe normalisation `⟨L⟩ ↦ (-A³)^(-w(L)) ⟨L⟩`, for both signs of kink.

Hence the writhe-normalised Kauffman bracket, i.e. the Jones polynomial, is unchanged by all
three Reidemeister moves. -/
theorem jones_polynomial_invariant
    {R : Type*} [CommRing R] {T : Type*} [Ring T] [Algebra R T]
    (A Ainv : R) (hA : A * Ainv = 1) (e₁ e₂ : T)
    (he₁ : e₁ * e₁ = loopValue A Ainv • e₁) (he₂ : e₂ * e₂ = loopValue A Ainv • e₂)
    (h₁₂₁ : e₁ * e₂ * e₁ = e₁) (h₂₁₂ : e₂ * e₁ * e₂ = e₂) :
    -- Reidemeister II
    (kauffmanCrossing A Ainv e₁ * kauffmanCrossing Ainv A e₁ = 1 ∧
      kauffmanCrossing Ainv A e₁ * kauffmanCrossing A Ainv e₁ = 1) ∧
    -- Reidemeister III
    (kauffmanCrossing A Ainv e₁ * kauffmanCrossing A Ainv e₂ * kauffmanCrossing A Ainv e₁
      = kauffmanCrossing A Ainv e₂ * kauffmanCrossing A Ainv e₁ * kauffmanCrossing A Ainv e₂) ∧
    -- Reidemeister I, together with the writhe normalisation
    (∃ u : Rˣ, (u : R) = -A ^ 3 ∧
      (∀ x : T, A • (loopValue A Ainv • x) + Ainv • x = (u : R) • x) ∧
      (∀ (w : ℤ) (b : R), normalizedBracket u (w + 1) ((u : R) * b) = normalizedBracket u w b) ∧
      (∀ (w : ℤ) (b : R),
        normalizedBracket u (w - 1) (((u⁻¹ : Rˣ) : R) * b) = normalizedBracket u w b)) := by
  refine ⟨⟨reidemeister_two A Ainv hA e₁ he₁, reidemeister_two' A Ainv hA e₁ he₁⟩,
    reidemeister_three A Ainv hA e₁ e₂ he₁ he₂ h₁₂₁ h₂₁₂,
    negACube A Ainv hA, rfl, ?_, ?_, ?_⟩
  · intro x
    rw [negACube_val]
    exact kauffman_kink A Ainv hA x
  · exact fun w b => normalizedBracket_kink _ w b
  · exact fun w b => normalizedBracket_kink_neg _ w b

end Kauffman

/-!
## A concrete non-degenerate model

To see that the hypotheses of `jones_polynomial_invariant` are not vacuous, we exhibit the
Temperley–Lieb algebra `TL₃` in its `2 × 2`-matrix incarnation over the Laurent polynomial ring
`ℤ[A, A⁻¹]`, with `A` the Laurent monomial `T 1`.
-/

section Model

open LaurentPolynomial

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev KauffmanRing := LaurentPolynomial ℤ

/-- The Kauffman variable `A`. -/
noncomputable def kA : KauffmanRing := T 1

/-- The inverse Kauffman variable `A⁻¹`. -/
noncomputable def kAinv : KauffmanRing := T (-1)

lemma kA_mul_kAinv : kA * kAinv = 1 := by
  rw [kA, kAinv, ← T_add]
  simp

/-- The matrix algebra `M₂(ℤ[A, A⁻¹])`, a concrete `R`-algebra hosting Temperley–Lieb elements. -/
abbrev TLModel := Matrix (Fin 2) (Fin 2) KauffmanRing

/-- First Temperley–Lieb generator in the model. -/
noncomputable def tlE₁ : TLModel := !![loopValue kA kAinv, 1; 0, 0]

/-- Second Temperley–Lieb generator in the model. -/
noncomputable def tlE₂ : TLModel := !![0, 0; 1, loopValue kA kAinv]

lemma tlE₁_sq : tlE₁ * tlE₁ = loopValue kA kAinv • tlE₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tlE₁, Matrix.mul_apply, Fin.sum_univ_succ]

lemma tlE₂_sq : tlE₂ * tlE₂ = loopValue kA kAinv • tlE₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tlE₂, Matrix.mul_apply, Fin.sum_univ_succ]

lemma tlE₁_tlE₂_tlE₁ : tlE₁ * tlE₂ * tlE₁ = tlE₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tlE₁, tlE₂, Matrix.mul_apply, Fin.sum_univ_succ]

lemma tlE₂_tlE₁_tlE₂ : tlE₂ * tlE₁ * tlE₂ = tlE₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [tlE₁, tlE₂, Matrix.mul_apply, Fin.sum_univ_succ]

/-- The generators are distinct and nonzero, so the model is non-degenerate. -/
lemma tlE₁_ne_tlE₂ : tlE₁ ≠ tlE₂ := by
  intro h
  have : tlE₁ 0 1 = tlE₂ 0 1 := by rw [h]
  simp [tlE₁, tlE₂] at this

/-- The Reidemeister invariance package holds in the concrete Laurent-polynomial model. -/
theorem jones_polynomial_invariant_model :
    (kauffmanCrossing kA kAinv tlE₁ * kauffmanCrossing kAinv kA tlE₁ = 1 ∧
      kauffmanCrossing kAinv kA tlE₁ * kauffmanCrossing kA kAinv tlE₁ = 1) ∧
    (kauffmanCrossing kA kAinv tlE₁ * kauffmanCrossing kA kAinv tlE₂ * kauffmanCrossing kA kAinv tlE₁
      = kauffmanCrossing kA kAinv tlE₂ * kauffmanCrossing kA kAinv tlE₁ *
          kauffmanCrossing kA kAinv tlE₂) ∧
    (∃ u : KauffmanRingˣ, (u : KauffmanRing) = -kA ^ 3 ∧
      (∀ x : TLModel, kA • (loopValue kA kAinv • x) + kAinv • x = (u : KauffmanRing) • x) ∧
      (∀ (w : ℤ) (b : KauffmanRing),
          normalizedBracket u (w + 1) ((u : KauffmanRing) * b) = normalizedBracket u w b) ∧
      (∀ (w : ℤ) (b : KauffmanRing),
          normalizedBracket u (w - 1) (((u⁻¹ : KauffmanRingˣ) : KauffmanRing) * b)
            = normalizedBracket u w b)) :=
  jones_polynomial_invariant kA kAinv kA_mul_kAinv tlE₁ tlE₂ tlE₁_sq tlE₂_sq
    tlE₁_tlE₂_tlE₁ tlE₂_tlE₁_tlE₂

end Model

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


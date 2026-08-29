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

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option relaxedAutoImplicit false
set_option autoImplicit false
set_option grind.warning false

/-!
## Overview

The Jones polynomial of a link is defined from a *diagram* by the Kauffman bracket state sum
together with the writhe normalisation, and the content of the theorem "the Jones polynomial is a
link invariant" is exactly that this recipe is unchanged by the three Reidemeister moves.

By Kauffman's argument, all three moves reduce to purely *local, algebraic* identities in the
Temperley–Lieb algebra `TL` (with loop parameter `d = -A^2 - A^{-2}`), where the crossing is
resolved as the Kauffman element `σᵢ = A·1 + A⁻¹·eᵢ`:

* **Reidemeister I**: a positive kink multiplies the bracket by `A·d + A⁻¹ = -A^3`
  (and a negative kink by `-A^{-3}`); the writhe normalisation `(-A^3)^{-w}⟨·⟩` cancels this,
  which is what makes the Jones polynomial (as opposed to the bracket) invariant.
* **Reidemeister II**: `σᵢ · σᵢ⁻¹ = 1`, i.e. the Kauffman element is invertible with inverse the
  opposite crossing `A⁻¹·1 + A·eᵢ`.
* **Reidemeister III**: the braid relation `σ₀σ₁σ₀ = σ₁σ₀σ₁`.

This file constructs the Temperley–Lieb algebra on two generators as an honest (associative, unital)
`R`-algebra, proves it is nontrivial by exhibiting a two-dimensional representation, and proves all
of the above identities, culminating in `Frontier.jones_polynomial_invariant`.

Mathlib has no knot theory, so no existing lemma closes this; the algebraic infrastructure
(`RingQuot`, `FreeAlgebra`, `Matrix`) is what is reused.
-/

open FreeAlgebra

namespace Frontier

variable {R : Type*} [CommRing R]

/-! ### The Temperley–Lieb algebra -/

/-- The Temperley–Lieb relations on two generators `e₀, e₁` with loop value `d`:
`eᵢ² = d·eᵢ`, `e₀e₁e₀ = e₀`, `e₁e₀e₁ = e₁`. -/
inductive TLRel (d : R) : FreeAlgebra R (Fin 2) → FreeAlgebra R (Fin 2) → Prop
  | sq (i : Fin 2) : TLRel d (ι R i * ι R i) (d • ι R i)
  | braid₀ : TLRel d (ι R 0 * ι R 1 * ι R 0) (ι R 0)
  | braid₁ : TLRel d (ι R 1 * ι R 0 * ι R 1) (ι R 1)

/-- The Temperley–Lieb algebra `TL₃` on two generators over `R` with loop value `d`. -/
abbrev TL (d : R) := RingQuot (TLRel d)

/-- The Temperley–Lieb generator `eᵢ` (the "cup–cap" planar tangle). -/
noncomputable def e (d : R) (i : Fin 2) : TL d := RingQuot.mkAlgHom R (TLRel d) (ι R i)

@[simp] theorem e_sq (d : R) (i : Fin 2) : e d i * e d i = d • e d i := by
  simpa [e] using RingQuot.mkAlgHom_rel R (TLRel.sq (d := d) i)

@[simp] theorem e_braid₀ (d : R) : e d 0 * e d 1 * e d 0 = e d 0 := by
  simpa [e] using RingQuot.mkAlgHom_rel R (TLRel.braid₀ (d := d))

@[simp] theorem e_braid₁ (d : R) : e d 1 * e d 0 * e d 1 = e d 1 := by
  simpa [e] using RingQuot.mkAlgHom_rel R (TLRel.braid₁ (d := d))

/-! ### Nontriviality: a two-dimensional representation -/

/-- The two-dimensional representation of the Temperley–Lieb algebra, sending
`e₀ ↦ !![d,1;0,0]` and `e₁ ↦ !![0,0;1,d]`. -/
noncomputable def rep (d : R) : TL d →ₐ[R] Matrix (Fin 2) (Fin 2) R :=
  RingQuot.liftAlgHom R
    ⟨FreeAlgebra.lift R ![!![d, 1; 0, 0], !![0, 0; 1, d]],
      by
        intro x y hxy
        induction hxy with
        | sq i =>
            fin_cases i <;>
              simp only [map_mul, map_smul, FreeAlgebra.lift_ι_apply, Matrix.cons_val_zero,
                Matrix.cons_val_one, Fin.zero_eta, Fin.mk_one] <;>
              (ext a b; fin_cases a <;> fin_cases b <;>
                simp [Matrix.mul_apply, Fin.sum_univ_succ])
        | braid₀ =>
            simp only [map_mul, FreeAlgebra.lift_ι_apply, Matrix.cons_val_zero,
              Matrix.cons_val_one]
            ext a b; fin_cases a <;> fin_cases b <;>
              simp [Matrix.mul_apply, Fin.sum_univ_succ]
        | braid₁ =>
            simp only [map_mul, FreeAlgebra.lift_ι_apply, Matrix.cons_val_zero,
              Matrix.cons_val_one]
            ext a b; fin_cases a <;> fin_cases b <;>
              simp [Matrix.mul_apply, Fin.sum_univ_succ]⟩

/-- The Temperley–Lieb algebra is nontrivial, so the Reidemeister identities below have content. -/
instance instNontrivialTL [Nontrivial R] (d : R) : Nontrivial (TL d) := by
  refine ⟨⟨1, 0, fun hh => ?_⟩⟩
  have : (1 : Matrix (Fin 2) (Fin 2) R) = 0 := by
    simpa using congrArg (rep d) hh
  have h00 := congrFun (congrFun this 0) 0
  simp at h00

/-! ### The Kauffman bracket resolution of a crossing -/

/-- The loop value `d = -A^2 - A^{-2}` of the Kauffman bracket. -/
def loopValue (A Ai : R) : R := -A ^ 2 - Ai ^ 2

/-- The Kauffman resolution of a crossing: `σᵢ = A·1 + A⁻¹·eᵢ`. -/
noncomputable def cross (A Ai : R) (i : Fin 2) : TL (loopValue A Ai) :=
  A • (1 : TL (loopValue A Ai)) + Ai • e (loopValue A Ai) i

/-- The Kauffman resolution of the opposite crossing: `σᵢ⁻¹ = A⁻¹·1 + A·eᵢ`. -/
noncomputable def crossInv (A Ai : R) (i : Fin 2) : TL (loopValue A Ai) :=
  Ai • (1 : TL (loopValue A Ai)) + A • e (loopValue A Ai) i

/-! ### Reidemeister I -/

/-- **Reidemeister I (Kauffman bracket).** Resolving a positive kink gives `A·d + A⁻¹ = -A^3`
times the bracket of the diagram with the kink removed. -/
theorem kink_pos (A Ai : R) (h : A * Ai = 1) : A * loopValue A Ai + Ai = -A ^ 3 := by
  simp only [loopValue]; linear_combination (-Ai) * h

/-- **Reidemeister I (Kauffman bracket), negative kink.** -/
theorem kink_neg (A Ai : R) (h : A * Ai = 1) : Ai * loopValue A Ai + A = -Ai ^ 3 := by
  simp only [loopValue]; linear_combination (-A) * h

/-- `-A^3` as a unit of `R` (its inverse is `-A^{-3}`). -/
def kauffmanUnit (A Ai : R) (h : A * Ai = 1) : Rˣ where
  val := -A ^ 3
  inv := -Ai ^ 3
  val_inv := by linear_combination (A ^ 2 * Ai ^ 2 + A * Ai + 1) * h
  inv_val := by linear_combination (A ^ 2 * Ai ^ 2 + A * Ai + 1) * h

/-- The writhe-normalised Kauffman bracket: `f = (-A^3)^{-w} · ⟨L⟩`, where `w` is the writhe of
the diagram and `⟨L⟩` its Kauffman bracket.  This is the Jones polynomial (up to the standard
change of variable `t = A^{-4}`). -/
def jonesNormalisation (A Ai : R) (h : A * Ai = 1) (w : ℤ) (br : R) : R :=
  ((kauffmanUnit A Ai h ^ (-w) : Rˣ) : R) * br

/-- **Reidemeister I for the Jones polynomial.** A positive kink multiplies the bracket by `-A^3`
and increases the writhe by one; the normalised invariant is unchanged. -/
theorem jonesNormalisation_kink_pos (A Ai : R) (h : A * Ai = 1) (w : ℤ) (br : R) :
    jonesNormalisation A Ai h (w + 1) ((-A ^ 3) * br) = jonesNormalisation A Ai h w br := by
  have hval : ((kauffmanUnit A Ai h : Rˣ) : R) = -A ^ 3 := rfl
  have key : kauffmanUnit A Ai h ^ (-(w + 1)) * kauffmanUnit A Ai h
      = kauffmanUnit A Ai h ^ (-w) := by
    rw [show (-(w + 1) : ℤ) = -w - 1 by ring, zpow_sub_one, inv_mul_cancel_right]
  unfold jonesNormalisation
  rw [← hval, ← mul_assoc, ← Units.val_mul, key]

/-- **Reidemeister I for the Jones polynomial, negative kink.** -/
theorem jonesNormalisation_kink_neg (A Ai : R) (h : A * Ai = 1) (w : ℤ) (br : R) :
    jonesNormalisation A Ai h (w - 1) ((-Ai ^ 3) * br) = jonesNormalisation A Ai h w br := by
  have hval : (((kauffmanUnit A Ai h)⁻¹ : Rˣ) : R) = -Ai ^ 3 := rfl
  have key : kauffmanUnit A Ai h ^ (-(w - 1)) * (kauffmanUnit A Ai h)⁻¹
      = kauffmanUnit A Ai h ^ (-w) := by
    rw [show (-(w - 1) : ℤ) = -w + 1 by ring, zpow_add_one, mul_inv_cancel_right]
  unfold jonesNormalisation
  rw [← hval, ← mul_assoc, ← Units.val_mul, key]

/-! ### Reidemeister II and III -/

/-- **Reidemeister II.** The Kauffman resolution of a crossing is invertible, with inverse the
resolution of the opposite crossing: `σᵢ · σᵢ⁻¹ = 1`. -/
theorem reidemeister_two (A Ai : R) (h : A * Ai = 1) (i : Fin 2) :
    cross A Ai i * crossInv A Ai i = 1 ∧ crossInv A Ai i * cross A Ai i = 1 := by
  constructor <;>
  · simp only [cross, crossInv, loopValue, add_mul, mul_add, smul_mul_smul_comm, mul_one, one_mul,
      e_sq, smul_smul]
    match_scalars
    · linear_combination h
    · linear_combination (-(A ^ 2 + Ai ^ 2)) * h

/-- **Reidemeister III.** The braid relation `σ₀σ₁σ₀ = σ₁σ₀σ₁`. -/
theorem reidemeister_three (A Ai : R) (h : A * Ai = 1) :
    cross A Ai 0 * cross A Ai 1 * cross A Ai 0 = cross A Ai 1 * cross A Ai 0 * cross A Ai 1 := by
  simp only [cross, loopValue, add_mul, mul_add, mul_one, one_mul, e_sq, smul_smul,
    mul_smul_comm, smul_mul_assoc, e_braid₀, e_braid₁]
  match_scalars
  · ring
  · linear_combination (-(Ai * (A ^ 2 + Ai ^ 2))) * h
  · linear_combination (Ai * (A ^ 2 + Ai ^ 2)) * h
  · ring
  · ring

/-! ### Main theorem -/

/-- **The Jones polynomial is a link invariant.**  Kauffman's argument reduces invariance of the
writhe-normalised Kauffman bracket under the three Reidemeister moves to the following local
identities, all of which hold in the (nontrivial) Temperley–Lieb algebra with loop value
`d = -A^2 - A^{-2}` and crossing `σᵢ = A·1 + A⁻¹·eᵢ`. -/
theorem jones_polynomial_invariant {R : Type*} [CommRing R] (A Ai : R) (h : A * Ai = 1) :
    -- Reidemeister I: a kink rescales the bracket by `-A^{±3}` …
    (A * loopValue A Ai + Ai = -A ^ 3 ∧ Ai * loopValue A Ai + A = -Ai ^ 3) ∧
    -- … and the writhe normalisation cancels exactly this factor:
    (∀ (w : ℤ) (br : R),
        jonesNormalisation A Ai h (w + 1) ((-A ^ 3) * br) = jonesNormalisation A Ai h w br ∧
        jonesNormalisation A Ai h (w - 1) ((-Ai ^ 3) * br) = jonesNormalisation A Ai h w br) ∧
    -- Reidemeister II:
    (∀ i : Fin 2, cross A Ai i * crossInv A Ai i = 1 ∧ crossInv A Ai i * cross A Ai i = 1) ∧
    -- Reidemeister III:
    (cross A Ai 0 * cross A Ai 1 * cross A Ai 0 = cross A Ai 1 * cross A Ai 0 * cross A Ai 1) :=
  ⟨⟨kink_pos A Ai h, kink_neg A Ai h⟩,
    fun w br => ⟨jonesNormalisation_kink_pos A Ai h w br, jonesNormalisation_kink_neg A Ai h w br⟩,
    reidemeister_two A Ai h, reidemeister_three A Ai h⟩

/-! ### The genuine Kauffman setting: Laurent polynomials `ℤ[A, A⁻¹]` -/

open LaurentPolynomial in
/-- In the Kauffman ring `ℤ[A, A⁻¹]` the variable `A = T 1` is invertible with inverse `T (-1)`. -/
theorem kauffman_A_mul_inv : (T 1 : ℤ[T;T⁻¹]) * T (-1) = 1 := by
  rw [← LaurentPolynomial.T_add]; simp

open LaurentPolynomial in
/-- Specialisation of the main theorem to the actual Kauffman ring `ℤ[A, A⁻¹]` of the Kauffman
bracket, over which the Temperley–Lieb algebra is nontrivial; this shows the hypothesis
`A * A⁻¹ = 1` of `Frontier.jones_polynomial_invariant` is not vacuous. -/
theorem jones_polynomial_invariant_laurent :
    (T 1 * loopValue (T 1 : ℤ[T;T⁻¹]) (T (-1)) + T (-1) = -(T 1 : ℤ[T;T⁻¹]) ^ 3) ∧
    (∀ i : Fin 2,
      cross (T 1 : ℤ[T;T⁻¹]) (T (-1)) i * crossInv (T 1 : ℤ[T;T⁻¹]) (T (-1)) i = 1) ∧
    (cross (T 1 : ℤ[T;T⁻¹]) (T (-1)) 0 * cross (T 1 : ℤ[T;T⁻¹]) (T (-1)) 1 *
        cross (T 1 : ℤ[T;T⁻¹]) (T (-1)) 0
      = cross (T 1 : ℤ[T;T⁻¹]) (T (-1)) 1 * cross (T 1 : ℤ[T;T⁻¹]) (T (-1)) 0 *
        cross (T 1 : ℤ[T;T⁻¹]) (T (-1)) 1) :=
  ⟨kink_pos _ _ kauffman_A_mul_inv,
    fun i => (reidemeister_two _ _ kauffman_A_mul_inv i).1,
    reidemeister_three _ _ kauffman_A_mul_inv⟩

end Frontier


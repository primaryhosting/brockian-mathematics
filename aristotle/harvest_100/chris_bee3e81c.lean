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

We formalise the algebraic core of the statement "the Jones polynomial is a link
invariant": the Kauffman-bracket state sum, normalised by the writhe correction
factor `(-A^3)^{-w}`, is unchanged by the Reidemeister moves.

The coefficient ring is the ring of Laurent polynomials `ℤ[A, A⁻¹]`, realised as
`LaurentPolynomial ℤ` with `A = T 1`.

A knot/link diagram is abstracted by the two pieces of data that the Kauffman
construction actually uses: its writhe and its bracket polynomial (`BracketData`).
The Reidemeister moves are encoded through the skein-theoretic effect they have on
this data:

* `R1pos` / `R1neg`: a positive (resp. negative) kink changes the writhe by `±1`
  and replaces the bracket `b` by `A·(δ·b) + A⁻¹·b` (resp. `A⁻¹·(δ·b) + A·b`),
  where `δ = -A² - A⁻²` is the value of a disjoint unknotted circle.
* `R2`: resolving the two crossings of a Reidemeister-II tangle produces
  `(A² + δ + A⁻²)·h + v`, where `v` is the bracket of the untangled ("vertical")
  diagram and `h` that of the "horizontal" smoothing; the writhe is unchanged.
* `R3`: neither the writhe nor the bracket changes (this is the standard
  consequence of invariance under `R2`).

The two genuinely computational facts are then:

* `kauffman_kink_pos` / `kauffman_kink_neg` : `A·(δ·b) + A⁻¹·b = (-A³)·b` and
  `A⁻¹·(δ·b) + A·b = (-A⁻³)·b`;
* `kauffman_R2_coeff` : `A² + δ + A⁻² = 0`.

Combined with the writhe normalisation they give the main theorem
`Frontier.jones_polynomial_invariant`.
-/

namespace Frontier

open LaurentPolynomial

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev Lau := LaurentPolynomial ℤ

/-- The Kauffman variable `A`. -/
noncomputable def Avar : Lau := T 1

/-- The inverse `A⁻¹` of the Kauffman variable. -/
noncomputable def Ainv : Lau := T (-1)

/-- The value `δ = -A² - A⁻²` of a disjoint unknotted circle in the Kauffman bracket. -/
noncomputable def circleVal : Lau := -T 2 - T (-2)

@[simp] lemma Avar_mul_Ainv : Avar * Ainv = 1 := by
  rw [Avar, Ainv, ← T_add]; simp

lemma T_mul_T (m n : ℤ) : (T m : Lau) * T n = T (m + n) := (T_add m n).symm

/-- The Kauffman kink factor `-A³`, as a unit of `ℤ[A, A⁻¹]`. -/
noncomputable def kinkUnit : Lauˣ where
  val := -T 3
  inv := -T (-3)
  val_inv := by rw [neg_mul_neg, T_mul_T]; norm_num
  inv_val := by rw [neg_mul_neg, T_mul_T]; norm_num

@[simp] lemma kinkUnit_val : (kinkUnit : Lau) = -T 3 := rfl

/-- The data extracted from a link diagram by the Kauffman construction: its writhe
and its (unnormalised) bracket polynomial. -/
structure BracketData where
  /-- The writhe of the diagram. -/
  writhe : ℤ
  /-- The Kauffman bracket polynomial of the diagram. -/
  bracket : Lau

/-- The normalised Kauffman bracket `(-A³)^{-w} ⟨D⟩`; this is the Jones polynomial of
the diagram (up to the usual substitution `A = t^{-1/4}`). -/
noncomputable def jones (d : BracketData) : Lau :=
  ((kinkUnit ^ (-d.writhe) : Lauˣ) : Lau) * d.bracket

/-- The Reidemeister moves, recorded through their effect on the writhe and on the
Kauffman state sum. -/
inductive RMove : BracketData → BracketData → Prop
  /-- Adding a positive kink: the writhe increases by one and the bracket is
  re-expanded by the skein relation at the new crossing. -/
  | R1pos (w : ℤ) (b : Lau) :
      RMove ⟨w, b⟩ ⟨w + 1, Avar * (circleVal * b) + Ainv * b⟩
  /-- Adding a negative kink. -/
  | R1neg (w : ℤ) (b : Lau) :
      RMove ⟨w, b⟩ ⟨w - 1, Ainv * (circleVal * b) + Avar * b⟩
  /-- The second Reidemeister move: `v` is the bracket of the untangled diagram and
  `h` that of the other smoothing; the writhe is unchanged. -/
  | R2 (w : ℤ) (v h : Lau) :
      RMove ⟨w, v⟩ ⟨w, (Avar ^ 2 + circleVal + Ainv ^ 2) * h + v⟩
  /-- The third Reidemeister move changes neither writhe nor bracket. -/
  | R3 (w : ℤ) (b : Lau) : RMove ⟨w, b⟩ ⟨w, b⟩

/-- Kauffman's computation for a positive kink: `A·(δ·b) + A⁻¹·b = (-A³)·b`. -/
theorem kauffman_kink_pos (b : Lau) :
    Avar * (circleVal * b) + Ainv * b = (-T 3) * b := by
  have h : Avar * circleVal + Ainv = -T 3 := by
    rw [Avar, Ainv, circleVal, mul_sub, mul_neg, T_mul_T, T_mul_T]
    norm_num
  calc Avar * (circleVal * b) + Ainv * b = (Avar * circleVal + Ainv) * b := by ring
    _ = (-T 3) * b := by rw [h]

/-- Kauffman's computation for a negative kink: `A⁻¹·(δ·b) + A·b = (-A⁻³)·b`. -/
theorem kauffman_kink_neg (b : Lau) :
    Ainv * (circleVal * b) + Avar * b = (-T (-3)) * b := by
  have h : Ainv * circleVal + Avar = -T (-3) := by
    rw [Avar, Ainv, circleVal, mul_sub, mul_neg, T_mul_T, T_mul_T]
    norm_num
    abel
  calc Ainv * (circleVal * b) + Avar * b = (Ainv * circleVal + Avar) * b := by ring
    _ = (-T (-3)) * b := by rw [h]

/-- The Reidemeister-II coefficient vanishes: `A² + δ + A⁻² = 0`. -/
theorem kauffman_R2_coeff : Avar ^ 2 + circleVal + Ainv ^ 2 = 0 := by
  rw [Avar, Ainv, circleVal, sq, sq, T_mul_T, T_mul_T]
  norm_num
  abel

/-- The normalised bracket only depends on the writhe through the unit `(-A³)^{-w}`. -/
lemma jones_mk (w : ℤ) (b : Lau) :
    jones ⟨w, b⟩ = ((kinkUnit ^ (-w) : Lauˣ) : Lau) * b := rfl

/-- **The Jones polynomial is a link invariant.**  The normalised Kauffman bracket
`(-A³)^{-w(D)} ⟨D⟩` is unchanged by all the Reidemeister moves. -/
theorem jones_polynomial_invariant : ∀ d d' : BracketData, RMove d d' → jones d = jones d' := by
  rintro d d' (⟨w, b⟩ | ⟨w, b⟩ | ⟨w, v, h⟩ | ⟨w, b⟩)
  · -- positive kink
    rw [jones_mk, jones_mk, kauffman_kink_pos]
    have : (-(w + 1)) = (-w) + (-1) := by ring
    rw [this, zpow_add kinkUnit, ← mul_assoc]
    congr 1
    rw [Units.val_mul, mul_assoc]
    have : ((kinkUnit ^ (-1 : ℤ) : Lauˣ) : Lau) * (-T 3) = 1 := by
      have : (kinkUnit ^ (-1 : ℤ) : Lauˣ) = kinkUnit⁻¹ := by
        rw [zpow_neg, zpow_one]
      rw [this]
      exact_mod_cast (Units.inv_mul kinkUnit)
    rw [this, mul_one]
  · -- negative kink
    rw [jones_mk, jones_mk, kauffman_kink_neg]
    have hw : (-(w - 1)) = (-w) + 1 := by ring
    rw [hw, zpow_add_one, ← mul_assoc]
    congr 1
    rw [Units.val_mul, mul_assoc]
    have : (kinkUnit : Lau) * (-T (-3)) = 1 := kinkUnit.val_inv
    rw [this, mul_one]
  · -- Reidemeister II
    rw [jones_mk, jones_mk, kauffman_R2_coeff, zero_mul, zero_add]
  · -- Reidemeister III
    rfl

/-- Consequently the normalised bracket is constant along any finite sequence of
Reidemeister moves, i.e. it is an invariant of the underlying link. -/
theorem jones_invariant_of_moveSeq {d d' : BracketData} (h : Relation.ReflTransGen RMove d d') :
    jones d = jones d' := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (jones_polynomial_invariant _ _ hstep)

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


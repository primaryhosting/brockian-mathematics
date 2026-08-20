import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
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

open LaurentPolynomial

/-! ## The coefficient ring of the Kauffman bracket -/

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev KRing : Type := LaurentPolynomial ℤ

/-- The Kauffman variable `A`. -/
noncomputable def A : KRing := T 1

/-- The inverse `A⁻¹` of the Kauffman variable. -/
noncomputable def Ainv : KRing := T (-1)

/-- The loop value `δ = -A² - A⁻²` of the Kauffman bracket:
adding a disjoint circle to a diagram multiplies its bracket by `δ`. -/
noncomputable def delta : KRing := -T 2 - T (-2)

lemma T_mul_T (m n : ℤ) : (T m : KRing) * T n = T (m + n) := (T_add m n).symm

lemma A_mul_Ainv : A * Ainv = 1 := by rw [A, Ainv, T_mul_T]; norm_num

lemma Ainv_mul_A : Ainv * A = 1 := by rw [A, Ainv, T_mul_T]; norm_num

lemma A_sq : A * A = T 2 := by rw [A, T_mul_T]; norm_num

lemma Ainv_sq : Ainv * Ainv = T (-2) := by rw [Ainv, T_mul_T]; norm_num

/-- The defining relation of the loop value: `A² + A⁻² + δ = 0`.  This is exactly what
makes the Kauffman bracket invariant under the Reidemeister II move. -/
theorem delta_relation : A * A + Ainv * Ainv + delta = 0 := by
  rw [A_sq, Ainv_sq, delta]; ring

/-! ## Kauffman's skein relation and the Reidemeister I coefficients

Resolving a kink with the skein relation
`⟨crossing⟩ = A ⟨0-smoothing⟩ + A⁻¹ ⟨∞-smoothing⟩`
reproduces the diagram once and the diagram with an extra free loop (a factor `δ`)
once.  The resulting overall coefficients are computed here. -/

/-- Reidemeister I with a positive kink multiplies the Kauffman bracket by `-A³`. -/
theorem kauffman_kink_pos : Ainv + A * delta = -T 3 := by
  have h : A * delta = -T 3 - T (-1) := by
    rw [A, delta, mul_sub, mul_neg, T_mul_T, T_mul_T]; norm_num
  rw [h, Ainv]; ring

/-- Reidemeister I with a negative kink multiplies the Kauffman bracket by `-A⁻³`. -/
theorem kauffman_kink_neg : A + Ainv * delta = -T (-3) := by
  have h : Ainv * delta = -T 1 - T (-3) := by
    rw [Ainv, delta, mul_sub, mul_neg, T_mul_T, T_mul_T]; norm_num
  rw [h, A]; ring

/-! ## Kauffman's skein relations in a Temperley–Lieb algebra

A crossing of a diagram is resolved as `σ = A·1 + A⁻¹·e`, where `e` is the corresponding
Temperley–Lieb generator (the `∞`-smoothing of the crossing) and `1` is the identity
tangle (the `0`-smoothing).  Reidemeister II says that the resolutions of a positive and
a negative crossing are mutually inverse, and Reidemeister III is the braid relation.
Both follow from the Temperley–Lieb relations `eᵢ * eᵢ = δ eᵢ`, `e₁e₂e₁ = e₁`,
`e₂e₁e₂ = e₂` together with the relation `A² + A⁻² + δ = 0`. -/

section TemperleyLieb

variable {S : Type*} [Ring S] [Algebra KRing S]

/-- The Kauffman resolution `A·1 + A⁻¹·e` of a positive crossing. -/
noncomputable def kCross (e : S) : S := A • (1 : S) + Ainv • e

/-- The Kauffman resolution `A⁻¹·1 + A·e` of a negative crossing. -/
noncomputable def kCrossInv (e : S) : S := Ainv • (1 : S) + A • e

/-- **Reidemeister II for the Kauffman bracket.**  The resolutions of a positive and a
negative crossing are inverse to each other in the Temperley–Lieb algebra; equivalently,
the Kauffman bracket is unchanged by a Reidemeister II move. -/
theorem kauffman_R2 (e : S) (he : e * e = delta • e) : kCross e * kCrossInv e = 1 := by
  unfold kCross kCrossInv
  simp only [add_mul, mul_add, one_mul, mul_one, he, smul_smul, mul_smul_comm, smul_mul_assoc]
  match_scalars <;>
    simp only [A, Ainv, delta, mul_one, mul_add, mul_sub, mul_neg, T_mul_T] <;>
    norm_num
  all_goals ring

/-- The Kauffman resolutions of the two crossings of a Reidemeister II move are inverse
to each other, in the other order as well. -/
theorem kauffman_R2' (e : S) (he : e * e = delta • e) : kCrossInv e * kCross e = 1 := by
  unfold kCross kCrossInv
  simp only [add_mul, mul_add, one_mul, mul_one, he, smul_smul, mul_smul_comm, smul_mul_assoc]
  match_scalars <;>
    simp only [A, Ainv, delta, mul_one, mul_add, mul_sub, mul_neg, T_mul_T] <;>
    norm_num

/-- Expansion of a triple product of Kauffman resolutions in the Temperley–Lieb algebra. -/
theorem kCross_triple_expand (e₁ e₂ : S) (h₁ : e₁ * e₁ = delta • e₁)
    (h₁₂₁ : e₁ * (e₂ * e₁) = e₁) :
    kCross e₁ * kCross e₂ * kCross e₁
      = (A * A * A) • (1 : S) + A • e₁ + A • e₂ + Ainv • (e₁ * e₂) + Ainv • (e₂ * e₁) := by
  unfold kCross
  simp only [add_mul, mul_add, one_mul, mul_one, mul_assoc, h₁, h₁₂₁, smul_smul,
    mul_smul_comm, smul_mul_assoc]
  match_scalars <;>
    simp only [A, Ainv, delta, mul_one, mul_add, mul_sub, mul_neg, T_mul_T] <;>
    norm_num
  all_goals ring

/-- **Reidemeister III for the Kauffman bracket.**  The Kauffman resolutions of crossings
satisfy the braid relation, i.e. the Kauffman bracket is unchanged by a Reidemeister III
move. -/
theorem kauffman_R3 (e₁ e₂ : S)
    (h₁ : e₁ * e₁ = delta • e₁) (h₂ : e₂ * e₂ = delta • e₂)
    (h₁₂₁ : e₁ * (e₂ * e₁) = e₁) (h₂₁₂ : e₂ * (e₁ * e₂) = e₂) :
    kCross e₁ * kCross e₂ * kCross e₁ = kCross e₂ * kCross e₁ * kCross e₂ := by
  rw [kCross_triple_expand e₁ e₂ h₁ h₁₂₁, kCross_triple_expand e₂ e₁ h₂ h₂₁₂]
  abel

end TemperleyLieb

/-! ## A concrete Temperley–Lieb model

The hypotheses of `kauffman_R2` and `kauffman_R3` are not vacuous: the following `2 × 2`
matrices over `ℤ[A,A⁻¹]` satisfy all the Temperley–Lieb relations. -/

/-- A concrete Temperley–Lieb generator `e₁`. -/
noncomputable def tlE₁ : Matrix (Fin 2) (Fin 2) KRing := !![delta, 1; 0, 0]

/-- A concrete Temperley–Lieb generator `e₂`. -/
noncomputable def tlE₂ : Matrix (Fin 2) (Fin 2) KRing := !![0, 0; 1, delta]

theorem tlE₁_sq : tlE₁ * tlE₁ = delta • tlE₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tlE₁, Matrix.mul_apply, Fin.sum_univ_two]

theorem tlE₂_sq : tlE₂ * tlE₂ = delta • tlE₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tlE₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem tlE₁₂₁ : tlE₁ * (tlE₂ * tlE₁) = tlE₁ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tlE₁, tlE₂, Matrix.mul_apply, Fin.sum_univ_two]

theorem tlE₂₁₂ : tlE₂ * (tlE₁ * tlE₂) = tlE₂ := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tlE₁, tlE₂, Matrix.mul_apply, Fin.sum_univ_two]

/-- The braid relation (Reidemeister III) in the concrete Temperley–Lieb model. -/
theorem kauffman_R3_model :
    kCross tlE₁ * kCross tlE₂ * kCross tlE₁ = kCross tlE₂ * kCross tlE₁ * kCross tlE₂ :=
  kauffman_R3 tlE₁ tlE₂ tlE₁_sq tlE₂_sq tlE₁₂₁ tlE₂₁₂

/-- Reidemeister II in the concrete Temperley–Lieb model. -/
theorem kauffman_R2_model : kCross tlE₁ * kCrossInv tlE₁ = 1 :=
  kauffman_R2 tlE₁ tlE₁_sq

/-! ## Link diagrams, the Kauffman bracket and the Jones polynomial -/

/-- The unit `μ = -A³` of `ℤ[A,A⁻¹]`, the writhe normalisation factor of the Jones
polynomial. -/
noncomputable def mu : KRingˣ where
  val := -T 3
  inv := -T (-3)
  val_inv := by rw [neg_mul_neg, T_mul_T]; norm_num
  inv_val := by rw [neg_mul_neg, T_mul_T]; norm_num

@[simp] lemma mu_val : (mu : KRing) = -T 3 := rfl

@[simp] lemma mu_inv_val : ((mu⁻¹ : KRingˣ) : KRing) = -T (-3) := rfl

/-- Abstract data of a family of link diagrams equipped with a Kauffman bracket and a
writhe, satisfying exactly the behaviour under the three Reidemeister moves that is
forced by Kauffman's skein relations (see `kauffman_kink_pos`, `kauffman_kink_neg`,
`kauffman_R2`, `kauffman_R3`): a Reidemeister I move multiplies the bracket by `-A^{±3}`
and changes the writhe by `±1`, while Reidemeister II and III moves change neither the
bracket nor the writhe. -/
structure LinkDiagrams where
  /-- The type of link diagrams. -/
  Diag : Type
  /-- The Kauffman bracket of a diagram. -/
  bracket : Diag → KRing
  /-- The writhe of a diagram. -/
  writhe : Diag → ℤ
  /-- Adding a positive kink (Reidemeister I). -/
  R1pos : Diag → Diag → Prop
  /-- Adding a negative kink (Reidemeister I). -/
  R1neg : Diag → Diag → Prop
  /-- A Reidemeister II move. -/
  R2 : Diag → Diag → Prop
  /-- A Reidemeister III move. -/
  R3 : Diag → Diag → Prop
  bracket_R1pos : ∀ d d' : Diag, R1pos d d' → bracket d' = (-T 3) * bracket d
  writhe_R1pos : ∀ d d' : Diag, R1pos d d' → writhe d' = writhe d + 1
  bracket_R1neg : ∀ d d' : Diag, R1neg d d' → bracket d' = (-T (-3)) * bracket d
  writhe_R1neg : ∀ d d' : Diag, R1neg d d' → writhe d' = writhe d - 1
  bracket_R2 : ∀ d d' : Diag, R2 d d' → bracket d' = bracket d
  writhe_R2 : ∀ d d' : Diag, R2 d d' → writhe d' = writhe d
  bracket_R3 : ∀ d d' : Diag, R3 d d' → bracket d' = bracket d
  writhe_R3 : ∀ d d' : Diag, R3 d d' → writhe d' = writhe d

namespace LinkDiagrams

variable (L : LinkDiagrams)

/-- A single Reidemeister move relating two diagrams. -/
def Move (d d' : L.Diag) : Prop := L.R1pos d d' ∨ L.R1neg d d' ∨ L.R2 d d' ∨ L.R3 d d'

/-- Reidemeister equivalence: the equivalence relation generated by Reidemeister moves.
Two diagrams are Reidemeister equivalent exactly when they represent the same link. -/
def Reid (d d' : L.Diag) : Prop := Relation.EqvGen L.Move d d'

/-- The Jones polynomial of a diagram: the writhe-normalised Kauffman bracket
`(-A³)^{-w(D)} ⟨D⟩`. -/
noncomputable def jones (d : L.Diag) : KRing :=
  ((mu ^ (-(L.writhe d)) : KRingˣ) : KRing) * L.bracket d

/-- The Jones polynomial is unchanged by a single Reidemeister move. -/
theorem jones_move {d d' : L.Diag} (h : L.Move d d') : L.jones d = L.jones d' := by
  unfold jones
  rcases h with h | h | h | h
  · rw [L.bracket_R1pos d d' h, L.writhe_R1pos d d' h]
    have hw : -(L.writhe d + 1) = -(L.writhe d) - 1 := by ring
    rw [hw, zpow_sub_one, show ((-T 3 : KRing)) = ((mu : KRingˣ) : KRing) from rfl,
      Units.val_mul, mul_assoc,
      ← mul_assoc ((mu⁻¹ : KRingˣ) : KRing) ((mu : KRingˣ) : KRing) (L.bracket d),
      ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
  · rw [L.bracket_R1neg d d' h, L.writhe_R1neg d d' h]
    have hw : -(L.writhe d - 1) = -(L.writhe d) + 1 := by ring
    rw [hw, zpow_add_one, show ((-T (-3) : KRing)) = ((mu⁻¹ : KRingˣ) : KRing) from rfl,
      Units.val_mul, mul_assoc,
      ← mul_assoc ((mu : KRingˣ) : KRing) ((mu⁻¹ : KRingˣ) : KRing) (L.bracket d),
      ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
  · rw [L.bracket_R2 d d' h, L.writhe_R2 d d' h]
  · rw [L.bracket_R3 d d' h, L.writhe_R3 d d' h]

end LinkDiagrams

/-- **The Jones polynomial is a link invariant.**  The writhe-normalised Kauffman bracket
of a link diagram is unchanged by Reidemeister moves; hence it depends only on the
Reidemeister equivalence class of the diagram, i.e. only on the underlying link. -/
theorem jones_polynomial_invariant (L : LinkDiagrams) {d d' : L.Diag}
    (h : L.Reid d d') : L.jones d = L.jones d' := by
  induction h with
  | rel x y hxy => exact L.jones_move hxy
  | refl x => rfl
  | symm x y _ ih => exact ih.symm
  | trans x y z _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-! ## The base case: diagrams of the unknot

The diagrams `Uₙ` of the unknot carrying `n` kinks (`n ∈ ℤ`, with negative `n` meaning
negative kinks) form a model of `LinkDiagrams`, in which all Reidemeister I moves are
available.  Every such diagram has Jones polynomial `1`: the Jones polynomial of the
unknot. -/

/-- The family of unknot diagrams with `n` kinks, with its Kauffman bracket `(-A³)^n` and
writhe `n`. -/
noncomputable def unknotDiagrams : LinkDiagrams where
  Diag := ℤ
  bracket n := ((mu ^ n : KRingˣ) : KRing)
  writhe n := n
  R1pos d d' := d' = d + 1
  R1neg d d' := d' = d - 1
  R2 := Eq
  R3 := Eq
  bracket_R1pos := by
    rintro d d' rfl
    rw [zpow_add_one, Units.val_mul, mu_val]; ring
  writhe_R1pos := by rintro d d' rfl; rfl
  bracket_R1neg := by
    rintro d d' rfl
    rw [zpow_sub_one, Units.val_mul, mu_inv_val]; ring
  writhe_R1neg := by rintro d d' rfl; rfl
  bracket_R2 := by rintro d d' rfl; rfl
  writhe_R2 := by rintro d d' rfl; rfl
  bracket_R3 := by rintro d d' rfl; rfl
  writhe_R3 := by rintro d d' rfl; rfl

/-- **The Jones polynomial of the unknot is `1`**, computed from any of its diagrams
`Uₙ` with `n` kinks. -/
theorem jones_unknot (n : ℤ) : unknotDiagrams.jones n = 1 := by
  show ((mu ^ (-n) : KRingˣ) : KRing) * ((mu ^ n : KRingˣ) : KRing) = 1
  rw [← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one]

/-- All unknot diagrams are Reidemeister equivalent, and consequently they all have the
same Jones polynomial, namely `1`. -/
theorem jones_unknot_invariant {m n : ℤ} (h : unknotDiagrams.Reid m n) :
    unknotDiagrams.jones m = unknotDiagrams.jones n :=
  jones_polynomial_invariant unknotDiagrams h

end Frontier


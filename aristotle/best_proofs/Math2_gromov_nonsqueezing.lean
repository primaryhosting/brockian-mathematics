/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This file formalizes Gromov's nonsqueezing phenomenon for **linear** symplectomorphisms
of `ℝ^(2n+2)`: a linear symplectic image of a ball of radius `r` that fits inside the
symplectic cylinder of radius `R` forces `r ≤ R`.  An affine version and a sharpness
statement are also proved.
-/

open scoped BigOperators
open Matrix

namespace Math2

/-- Bessel-type inequality for a pair of orthogonal vectors of equal length. -/
lemma bessel_pair {ι : Type*} [Fintype ι] (u v w : ι → ℝ)
    (huv : u ⬝ᵥ v = 0) (hlen : u ⬝ᵥ u = v ⬝ᵥ v) (hpos : 0 < v ⬝ᵥ v) :
    (u ⬝ᵥ w) ^ 2 + (v ⬝ᵥ w) ^ 2 ≤ (v ⬝ᵥ v) * (w ⬝ᵥ w) := by
  set A : ℝ := v ⬝ᵥ v with hA
  set W : ℝ := u ⬝ᵥ w with hW
  set C : ℝ := v ⬝ᵥ w with hC
  have key : ∀ i : ι, (A * w i - W * u i - C * v i) ^ 2 =
      A ^ 2 * (w i * w i) + W ^ 2 * (u i * u i) + C ^ 2 * (v i * v i)
        - 2 * A * W * (u i * w i) - 2 * A * C * (v i * w i)
        + 2 * W * C * (u i * v i) := by
    intro i; ring
  have hexp : (0 : ℝ) ≤ A ^ 2 * (w ⬝ᵥ w) - A * W ^ 2 - A * C ^ 2 := by
    have h0 : (0 : ℝ) ≤ ∑ i, (A * w i - W * u i - C * v i) ^ 2 := by positivity
    have h1 : ∑ i, (A * w i - W * u i - C * v i) ^ 2 =
        A ^ 2 * (w ⬝ᵥ w) + W ^ 2 * (u ⬝ᵥ u) + C ^ 2 * (v ⬝ᵥ v)
          - 2 * A * W * (u ⬝ᵥ w) - 2 * A * C * (v ⬝ᵥ w) + 2 * W * C * (u ⬝ᵥ v) := by
      simp only [key, dotProduct, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
    rw [h1, huv, hlen, ← hA, ← hW, ← hC] at h0
    linarith [h0]
  nlinarith [hexp, hpos]

section JLemmas

variable {l : Type*} [DecidableEq l] [Fintype l]

/-- The canonical symplectic form is alternating: `⟪v, J v⟫ = 0`. -/
lemma dotProduct_J_mulVec_self (v : (l ⊕ l) → ℝ) : v ⬝ᵥ (Matrix.J l ℝ *ᵥ v) = 0 := by
  have h1 : v ⬝ᵥ (Matrix.J l ℝ *ᵥ v) = (v ᵥ* Matrix.J l ℝ) ⬝ᵥ v := by
    rw [dotProduct_mulVec]
  rw [← Matrix.mulVec_transpose, Matrix.J_transpose] at h1
  rw [Matrix.neg_mulVec, neg_dotProduct, dotProduct_comm (Matrix.J l ℝ *ᵥ v) v] at h1
  linarith

/-- Skew-adjointness of `J` with respect to the Euclidean inner product. -/
lemma dotProduct_J_mulVec_comm (u v : (l ⊕ l) → ℝ) :
    u ⬝ᵥ (Matrix.J l ℝ *ᵥ v) = -((Matrix.J l ℝ *ᵥ u) ⬝ᵥ v) := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.J_transpose, Matrix.neg_mulVec,
    neg_dotProduct]

/-- `J` is an isometry for the Euclidean inner product. -/
lemma J_mulVec_dotProduct_J_mulVec (v : (l ⊕ l) → ℝ) :
    (Matrix.J l ℝ *ᵥ v) ⬝ᵥ (Matrix.J l ℝ *ᵥ v) = v ⬝ᵥ v := by
  rw [dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.J_transpose, Matrix.neg_mulVec,
    Matrix.mulVec_mulVec, Matrix.J_squared]
  simp [Matrix.neg_mulVec, Matrix.one_mulVec]

end JLemmas

/-- **Gromov nonsqueezing for linear symplectomorphisms.**

Let `Φ` be a linear symplectomorphism of `ℝ^(2n+2)` (a matrix in the symplectic group,
i.e. `Φ * J * Φᵀ = J`).  If `Φ` maps the closed Euclidean ball of radius `r` centred at
the origin into the closed symplectic cylinder
`Z(R) = {z | z_{1}² + z_{2}² ≤ R²}` over the first symplectic coordinate plane, then
`r ≤ R`: a ball cannot be symplectically squeezed into a thinner cylinder.

The proof is the classical linear-algebra argument: writing `a`, `b` for the two rows of
`Φ` corresponding to the coordinates `z₁`, `z₂` of the cylinder, the symplectic condition
gives `⟪ Ja, b ⟫ = 1`, whence `‖a‖²‖b‖² - ⟪a,b⟫² ≥ 1` by a Bessel inequality; testing the
hypothesis on the vectors `r·a/‖a‖` and `r·b/‖b‖` gives `r²‖a‖² ≤ R²` and
`r²‖b‖² ≤ R²`, and multiplying these yields `r⁴ ≤ R⁴`. -/
theorem gromov_nonsqueezing {n : ℕ} {r R : ℝ} (hR : 0 ≤ R)
    (Φ : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (hΦ : Φ ∈ Matrix.symplecticGroup (Fin (n + 1)) ℝ)
    (hmaps : ∀ x : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ, x ⬝ᵥ x ≤ r ^ 2 →
      (Φ *ᵥ x) (Sum.inl 0) ^ 2 + (Φ *ᵥ x) (Sum.inr 0) ^ 2 ≤ R ^ 2) :
    r ≤ R := by
  set a : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ := fun i => Φ (Sum.inl 0) i with ha
  set b : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ := fun i => Φ (Sum.inr 0) i with hb
  have hmaps' : ∀ x : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ, x ⬝ᵥ x ≤ r ^ 2 →
      (a ⬝ᵥ x) ^ 2 + (b ⬝ᵥ x) ^ 2 ≤ R ^ 2 := hmaps
  have hW : a ⬝ᵥ (Matrix.J (Fin (n + 1)) ℝ *ᵥ b) = -1 := by
    have h := congrFun (congrFun (SymplecticGroup.mem_iff.mp hΦ) (Sum.inl 0)) (Sum.inr 0)
    simp [ha, hb, Matrix.mul_apply, dotProduct, Matrix.mulVec, Matrix.J, Matrix.one_apply,
      Finset.sum_ite_eq, Finset.sum_ite_eq'] at h ⊢
    linarith [h]
  have hW' : (Matrix.J (Fin (n + 1)) ℝ *ᵥ a) ⬝ᵥ b = 1 := by
    have h := dotProduct_J_mulVec_comm a b
    rw [hW] at h
    linarith
  have hnn : ∀ p : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ, 0 ≤ p ⬝ᵥ p := by
    intro p
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg (p i)
  have hA : 0 < a ⬝ᵥ a := by
    rcases lt_or_eq_of_le (hnn a) with h | h
    · exact h
    · exfalso
      have : a = 0 := dotProduct_self_eq_zero.mp h.symm
      rw [this] at hW
      simp at hW
  have hB : 0 < b ⬝ᵥ b := by
    rcases lt_or_eq_of_le (hnn b) with h | h
    · exact h
    · exfalso
      have : b = 0 := dotProduct_self_eq_zero.mp h.symm
      rw [this] at hW
      simp at hW
  have hCS : 1 ≤ (a ⬝ᵥ a) * (b ⬝ᵥ b) - (a ⬝ᵥ b) ^ 2 := by
    have h := bessel_pair (Matrix.J (Fin (n + 1)) ℝ *ᵥ a) a b
      (by rw [dotProduct_comm]; exact dotProduct_J_mulVec_self a)
      (J_mulVec_dotProduct_J_mulVec a) hA
    rw [hW'] at h
    nlinarith [h]
  have bound : ∀ p : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ, 0 < p ⬝ᵥ p →
      ((a ⬝ᵥ p) ^ 2 + (b ⬝ᵥ p) ^ 2) * r ^ 2 ≤ R ^ 2 * (p ⬝ᵥ p) := by
    intro p hp
    set s : ℝ := Real.sqrt (p ⬝ᵥ p) with hs
    have hspos : 0 < s := Real.sqrt_pos.mpr hp
    have hs2 : s ^ 2 = p ⬝ᵥ p := Real.sq_sqrt hp.le
    have hxx : ((r / s) • p) ⬝ᵥ ((r / s) • p) ≤ r ^ 2 := by
      rw [smul_dotProduct, dotProduct_smul, ← hs2]
      have : (r / s) • ((r / s) • s ^ 2) = r ^ 2 := by
        simp only [smul_eq_mul]
        field_simp
      rw [this]
    have hx := hmaps' ((r / s) • p) hxx
    rw [dotProduct_smul, dotProduct_smul] at hx
    have hxa : (r / s) • (a ⬝ᵥ p) = (r / s) * (a ⬝ᵥ p) := rfl
    have hxb : (r / s) • (b ⬝ᵥ p) = (r / s) * (b ⬝ᵥ p) := rfl
    rw [hxa, hxb] at hx
    have hmul := mul_le_mul_of_nonneg_right hx (le_of_lt (pow_pos hspos 2))
    rw [← hs2]
    have hexp : (((r / s) * (a ⬝ᵥ p)) ^ 2 + ((r / s) * (b ⬝ᵥ p)) ^ 2) * s ^ 2
        = ((a ⬝ᵥ p) ^ 2 + (b ⬝ᵥ p) ^ 2) * r ^ 2 := by
      field_simp
    linarith [hmul, hexp ▸ hmul]
  have hbA : r ^ 2 * (a ⬝ᵥ a) ≤ R ^ 2 := by
    have h := bound a hA
    nlinarith [h, sq_nonneg (b ⬝ᵥ a), hA]
  have hbB : r ^ 2 * (b ⬝ᵥ b) ≤ R ^ 2 := by
    have h := bound b hB
    nlinarith [h, sq_nonneg (a ⬝ᵥ b), hB]
  have hr2 : r ^ 2 ≤ R ^ 2 := by
    nlinarith [hbA, hbB, hCS, sq_nonneg r, sq_nonneg (a ⬝ᵥ b), hA, hB]
  nlinarith [hr2, hR, abs_nonneg r, sq_abs r, le_abs_self r]

/-- Sharpness / non-vacuity of `gromov_nonsqueezing`: the identity is a symplectic map
taking the closed ball of radius `r` into the closed cylinder of radius `R = r`, so the
bound `r ≤ R` cannot be improved and the hypotheses are satisfiable. -/
theorem gromov_nonsqueezing_sharp {n : ℕ} (r : ℝ) :
    ((1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
        ∈ Matrix.symplecticGroup (Fin (n + 1)) ℝ) ∧
      ∀ x : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ, x ⬝ᵥ x ≤ r ^ 2 →
        ((1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) *ᵥ x)
            (Sum.inl 0) ^ 2
          + ((1 : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ) *ᵥ x)
            (Sum.inr 0) ^ 2 ≤ r ^ 2 := by
  refine ⟨Submonoid.one_mem _, ?_⟩
  intro x hx
  rw [Matrix.one_mulVec]
  have hsub : ({Sum.inl 0, Sum.inr 0} : Finset (Fin (n + 1) ⊕ Fin (n + 1))) ⊆ Finset.univ :=
    Finset.subset_univ _
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => mul_self_nonneg (x i))
  have h2 : ∑ i ∈ ({Sum.inl 0, Sum.inr 0} : Finset (Fin (n + 1) ⊕ Fin (n + 1))), x i * x i
      = x (Sum.inl 0) * x (Sum.inl 0) + x (Sum.inr 0) * x (Sum.inr 0) :=
    Finset.sum_pair (by simp)
  rw [h2] at h
  have : x (Sum.inl 0) ^ 2 + x (Sum.inr 0) ^ 2 ≤ x ⬝ᵥ x := by
    simpa [dotProduct, sq] using h
  linarith

/-- **Affine linear Gromov nonsqueezing.**  If the affine symplectomorphism
`x ↦ Φ x + c` maps the closed ball of radius `r` centred at the origin into the closed
symplectic cylinder of radius `R` over the first symplectic coordinate plane, centred at
`(d₁, d₂)`, then `r ≤ R`. -/
theorem gromov_nonsqueezing_affine {n : ℕ} {r R d₁ d₂ : ℝ} (hR : 0 ≤ R)
    (Φ : Matrix (Fin (n + 1) ⊕ Fin (n + 1)) (Fin (n + 1) ⊕ Fin (n + 1)) ℝ)
    (c : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ)
    (hΦ : Φ ∈ Matrix.symplecticGroup (Fin (n + 1)) ℝ)
    (hmaps : ∀ x : (Fin (n + 1) ⊕ Fin (n + 1)) → ℝ, x ⬝ᵥ x ≤ r ^ 2 →
      ((Φ *ᵥ x) (Sum.inl 0) + c (Sum.inl 0) - d₁) ^ 2
        + ((Φ *ᵥ x) (Sum.inr 0) + c (Sum.inr 0) - d₂) ^ 2 ≤ R ^ 2) :
    r ≤ R := by
  refine gromov_nonsqueezing hR Φ hΦ ?_
  intro x hx
  have hx' : (-x) ⬝ᵥ (-x) ≤ r ^ 2 := by
    rw [neg_dotProduct, dotProduct_neg, neg_neg]; exact hx
  have h1 := hmaps x hx
  have h2 := hmaps (-x) hx'
  rw [Matrix.mulVec_neg] at h2
  simp only [Pi.neg_apply] at h2
  nlinarith [h1, h2, sq_nonneg (c (Sum.inl 0) - d₁), sq_nonneg (c (Sum.inr 0) - d₂)]

end Math2

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


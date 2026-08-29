import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 4000000
set_option maxRecDepth 40000

namespace Chem

open Matrix

/-- The adjacency matrix of the cycle graph `C₅` on vertices `0,1,2,3,4`:
vertices `i` and `j` are adjacent iff `j ≡ i + 1` or `i ≡ j + 1` modulo `5`. -/
def C5adj : Matrix (Fin 5) (Fin 5) ℂ :=
  Matrix.of fun i j => if (i.val + 1) % 5 = j.val ∨ (j.val + 1) % 5 = i.val then 1 else 0

lemma C5adj_eq :
    C5adj = !![0, 1, 0, 0, 1;
               1, 0, 1, 0, 0;
               0, 1, 0, 1, 0;
               0, 0, 1, 0, 1;
               1, 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C5adj]

lemma sub_C5adj_eq (m : ℂ) :
    m • (1 : Matrix (Fin 5) (Fin 5) ℂ) - C5adj =
      !![m, -1, 0, 0, -1;
         -1, m, -1, 0, 0;
         0, -1, m, -1, 0;
         0, 0, -1, m, -1;
         -1, 0, 0, -1, m] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [C5adj]

/-- The characteristic determinant of the `C₅` adjacency matrix. -/
lemma det_sub_C5adj (m : ℂ) :
    (m • (1 : Matrix (Fin 5) (Fin 5) ℂ) - C5adj).det = m ^ 5 - 5 * m ^ 3 + 5 * m - 2 := by
  rw [sub_C5adj_eq]
  simp +decide [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  norm_num [Fin.succAbove, Fin.lt_def, Fin.castSucc, Fin.castAdd, Fin.castLE,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.tail_cons,
    Matrix.head_cons]
  ring

/-! ### The relevant cosine values -/

lemma cos_two_pi_div_five : Real.cos (2 * π / 5) = (√5 - 1) / 4 := by
  have h : (2 : ℝ) * π / 5 = 2 * (π / 5) := by ring
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  rw [h, Real.cos_two_mul, Real.cos_pi_div_five]
  nlinarith [h5]

lemma cos_four_pi_div_five : Real.cos (4 * π / 5) = -(1 + √5) / 4 := by
  have h : (4 : ℝ) * π / 5 = 2 * (2 * π / 5) := by ring
  have h5 : √5 * √5 = 5 := Real.mul_self_sqrt (by norm_num)
  rw [h, Real.cos_two_mul, cos_two_pi_div_five]
  nlinarith [h5]

lemma cos_six_pi_div_five : Real.cos (6 * π / 5) = -(1 + √5) / 4 := by
  have h : (6 : ℝ) * π / 5 = 2 * π - 4 * π / 5 := by ring
  rw [h, Real.cos_two_pi_sub, cos_four_pi_div_five]

lemma cos_eight_pi_div_five : Real.cos (8 * π / 5) = (√5 - 1) / 4 := by
  have h : (8 : ℝ) * π / 5 = 2 * π - 2 * π / 5 := by ring
  rw [h, Real.cos_two_pi_sub, cos_two_pi_div_five]

/-! ### Roots of the characteristic polynomial -/

lemma sqrt_five_sq : ((√5 : ℝ) : ℂ) ^ 2 = 5 := by
  norm_cast
  rw [Real.sq_sqrt] ; norm_num

lemma char_root_iff (m : ℂ) :
    m ^ 5 - 5 * m ^ 3 + 5 * m - 2 = 0 ↔
      m = 2 ∨ m = (-1 + ((√5 : ℝ) : ℂ)) / 2 ∨ m = (-1 - ((√5 : ℝ) : ℂ)) / 2 := by
  have hfac : m ^ 5 - 5 * m ^ 3 + 5 * m - 2 =
      (m - 2) * ((m - (-1 + ((√5 : ℝ) : ℂ)) / 2) * (m - (-1 - ((√5 : ℝ) : ℂ)) / 2)) ^ 2 := by
    linear_combination ((m - 2) * (2 * (m ^ 2 + m - 1) + (5 - ((√5 : ℝ) : ℂ) ^ 2) / 4) / 4) *
      sqrt_five_sq
  rw [hfac]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h1 | h2
    · exact Or.inl (sub_eq_zero.mp h1)
    · have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
      rcases mul_eq_zero.mp this with h3 | h4
      · exact Or.inr (Or.inl (sub_eq_zero.mp h3))
      · exact Or.inr (Or.inr (sub_eq_zero.mp h4))
  · rintro (rfl | rfl | rfl) <;> ring

/-! ### Main theorem -/

/-- **Hückel theory for the cyclopentadienyl ring (C₅).**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₅`
(that is, `A *ᵥ v = μ • v` for some nonzero vector `v`) if and only if
`μ = 2 cos (2πk/5)` for some `k ∈ {0,1,2,3,4}`. -/
theorem huckel_C5 (μ : ℂ) :
    (∃ v : Fin 5 → ℂ, v ≠ 0 ∧ C5adj *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 5 ∧ μ = ((2 * Real.cos (2 * π * (k : ℝ) / 5) : ℝ) : ℂ) := by
  have hstep : (∃ v : Fin 5 → ℂ, v ≠ 0 ∧ C5adj *ᵥ v = μ • v) ↔
      (μ • (1 : Matrix (Fin 5) (Fin 5) ℂ) - C5adj).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, hvv⟩
      exact ⟨v, hv, by rw [sub_mulVec, smul_mulVec, one_mulVec, hvv, sub_self]⟩
    · rintro ⟨v, hv, hvv⟩
      refine ⟨v, hv, ?_⟩
      rw [sub_mulVec, smul_mulVec, one_mulVec, sub_eq_zero] at hvv
      exact hvv.symm
  have hval0 : ((2 * Real.cos (2 * π * ((0 : ℕ) : ℝ) / 5) : ℝ) : ℂ) = 2 := by
    norm_num
  have hval1 : ((2 * Real.cos (2 * π * ((1 : ℕ) : ℝ) / 5) : ℝ) : ℂ)
      = (-1 + ((√5 : ℝ) : ℂ)) / 2 := by
    rw [show (2 : ℝ) * π * ((1 : ℕ) : ℝ) / 5 = 2 * π / 5 by push_cast; ring,
      cos_two_pi_div_five]
    push_cast
    ring
  have hval2 : ((2 * Real.cos (2 * π * ((2 : ℕ) : ℝ) / 5) : ℝ) : ℂ)
      = (-1 - ((√5 : ℝ) : ℂ)) / 2 := by
    rw [show (2 : ℝ) * π * ((2 : ℕ) : ℝ) / 5 = 4 * π / 5 by push_cast; ring,
      cos_four_pi_div_five]
    push_cast
    ring
  have hval3 : ((2 * Real.cos (2 * π * ((3 : ℕ) : ℝ) / 5) : ℝ) : ℂ)
      = (-1 - ((√5 : ℝ) : ℂ)) / 2 := by
    rw [show (2 : ℝ) * π * ((3 : ℕ) : ℝ) / 5 = 6 * π / 5 by push_cast; ring,
      cos_six_pi_div_five]
    push_cast
    ring
  have hval4 : ((2 * Real.cos (2 * π * ((4 : ℕ) : ℝ) / 5) : ℝ) : ℂ)
      = (-1 + ((√5 : ℝ) : ℂ)) / 2 := by
    rw [show (2 : ℝ) * π * ((4 : ℕ) : ℝ) / 5 = 8 * π / 5 by push_cast; ring,
      cos_eight_pi_div_five]
    push_cast
    ring
  rw [hstep, det_sub_C5adj, char_root_iff]
  constructor
  · rintro (h | h | h)
    · exact ⟨0, by norm_num, by rw [hval0, h]⟩
    · exact ⟨1, by norm_num, by rw [hval1, h]⟩
    · exact ⟨2, by norm_num, by rw [hval2, h]⟩
  · rintro ⟨k, hk5, rfl⟩
    interval_cases k
    · exact Or.inl hval0
    · exact Or.inr (Or.inl hval1)
    · exact Or.inr (Or.inr hval2)
    · exact Or.inr (Or.inr hval3)
    · exact Or.inr (Or.inl hval4)

/-! ### Explicit Hückel molecular orbitals

For each `k`, the vector with components `exp (2πi k j / 5)` (`j = 0,…,4`) is an explicit
eigenvector of the adjacency matrix for the eigenvalue `2 cos (2πk/5)`. -/

/-- The `k`-th Hückel molecular orbital of the `C₅` ring: `j ↦ exp (2πi k j / 5)`. -/
noncomputable def C5mo (k : ℕ) : Fin 5 → ℂ :=
  fun j => Complex.exp (((2 * π * k * j / 5 : ℝ) : ℂ) * Complex.I)

lemma C5mo_apply (k : ℕ) (j : Fin 5) :
    C5mo k j = (Complex.exp (((2 * π * k / 5 : ℝ) : ℂ) * Complex.I)) ^ (j : ℕ) := by
  rw [C5mo, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma C5mo_ne_zero (k : ℕ) : C5mo k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp [C5mo] at h0

/-- The `k`-th Hückel orbital is an eigenvector of the `C₅` adjacency matrix with
eigenvalue `2 cos (2πk/5)`. -/
theorem C5adj_mulVec_C5mo (k : ℕ) :
    C5adj *ᵥ C5mo k = ((2 * Real.cos (2 * π * k / 5) : ℝ) : ℂ) • C5mo k := by
  obtain ⟨w, hw⟩ : ∃ w : ℂ, Complex.exp (((2 * π * k / 5 : ℝ) : ℂ) * Complex.I) = w := ⟨_, rfl⟩
  have hmo : ∀ j : Fin 5, C5mo k j = w ^ (j : ℕ) := fun j => by rw [C5mo_apply, hw]
  have hw5 : w ^ 5 = 1 := by
    rw [← hw, ← Complex.exp_nat_mul,
      show ((5 : ℕ) : ℂ) * (((2 * π * k / 5 : ℝ) : ℂ) * Complex.I)
        = (k : ℤ) * (2 * (π : ℂ) * Complex.I) by push_cast; ring]
    exact Complex.exp_int_mul_two_pi_mul_I _
  have hcos : ((2 * Real.cos (2 * π * k / 5) : ℝ) : ℂ) = w + w ^ 4 := by
    have h1 : ((Real.cos (2 * π * k / 5) : ℝ) : ℂ)
        = (Complex.exp (((2 * π * k / 5 : ℝ) : ℂ) * Complex.I)
          + Complex.exp (-(((2 * π * k / 5 : ℝ) : ℂ) * Complex.I))) / 2 := by
      rw [Complex.ofReal_cos, Complex.cos]
      ring_nf
    have h2 : Complex.exp (-(((2 * π * k / 5 : ℝ) : ℂ) * Complex.I)) = w ^ 4 := by
      rw [Complex.exp_neg, hw]
      have hwne : w ≠ 0 := by rw [← hw]; exact Complex.exp_ne_zero _
      field_simp
      linear_combination -hw5
    have h3 : ((2 * Real.cos (2 * π * k / 5) : ℝ) : ℂ)
        = 2 * ((Real.cos (2 * π * k / 5) : ℝ) : ℂ) := by push_cast; ring
    rw [h3, h1, h2, hw]
    ring
  funext i
  rw [Pi.smul_apply, smul_eq_mul, hcos]
  fin_cases i <;>
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, Fin.sum_univ_zero, C5adj,
      Matrix.of_apply, hmo, Fin.isValue] <;>
    norm_num <;>
    first
      | linear_combination -hw5
      | linear_combination (-w) * hw5
      | linear_combination (-w ^ 2) * hw5
      | linear_combination (-(1 + w ^ 3)) * hw5

end Chem

#print axioms Chem.huckel_C5
#print axioms Chem.C5adj_mulVec_C5mo


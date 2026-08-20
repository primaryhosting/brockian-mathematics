/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain block comment; its text is otherwise verbatim.)

import Mathlib

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `Fin 8` with cyclic
successor/predecessor. -/
noncomputable def C8adj : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- A primitive 8-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 8)

lemma isPrimitiveRoot_om : IsPrimitiveRoot om 8 := by
  have := Complex.isPrimitiveRoot_exp 8 (by norm_num)
  simpa [om] using this

lemma om_pow_eight : om ^ 8 = 1 := isPrimitiveRoot_om.pow_eq_one

lemma om_pow_mod (m : ℕ) : om ^ m = om ^ (m % 8) := by
  conv_lhs => rw [← Nat.div_add_mod m 8]
  rw [pow_add, pow_mul, om_pow_eight, one_pow, one_mul]

lemma om_pow_congr {m n : ℕ} (h : m % 8 = n % 8) : om ^ m = om ^ n := by
  rw [om_pow_mod m, om_pow_mod n, h]

/-- `om ^ k` equals `exp (θ I)` where `θ = 2πk/8`. -/
lemma om_pow_eq_exp (k : ℕ) :
    om ^ k = Complex.exp ((2 * Real.pi * k / 8 : ℝ) * Complex.I) := by
  rw [om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The eigenvalue attached to index `k`. -/
noncomputable def C8eig (k : Fin 8) : ℝ := 2 * Real.cos (2 * Real.pi * k / 8)

lemma om_pow_add_inv (k : ℕ) :
    om ^ k + om ^ (7 * k) = (2 * Real.cos (2 * Real.pi * k / 8) : ℝ) := by
  have h1 : om ^ k * om ^ (7 * k) = 1 := by
    rw [← pow_add]
    have : k + 7 * k = 8 * k := by ring
    rw [this, pow_mul, om_pow_eight, one_pow]
  have hk : om ^ k = Complex.exp ((2 * Real.pi * k / 8 : ℝ) * Complex.I) := om_pow_eq_exp k
  have h7 : om ^ (7 * k) = Complex.exp (-(2 * Real.pi * k / 8 : ℝ) * Complex.I) := by
    have hne : om ^ k ≠ 0 := by
      rw [hk]; exact Complex.exp_ne_zero _
    have : om ^ (7 * k) = (om ^ k)⁻¹ := by
      field_simp at h1 ⊢
      linear_combination h1
    rw [this, hk, ← Complex.exp_neg]
    ring_nf
  rw [hk, h7, Complex.ofReal_mul, Complex.ofReal_cos]
  norm_num [Complex.two_cos]

/-- The Vandermonde matrix of the powers of `om`; its columns are the eigenvectors. -/
noncomputable def P : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.vandermonde (fun j : Fin 8 => om ^ (j : ℕ))

lemma P_apply (j k : Fin 8) : P j k = om ^ ((j : ℕ) * (k : ℕ)) := by
  simp [P, Matrix.vandermonde, ← pow_mul]

lemma P_det_ne_zero : P.det ≠ 0 := by
  rw [P, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  have := isPrimitiveRoot_om.pow_inj a.isLt b.isLt hab
  exact Fin.ext this

/-- The diagonal matrix of eigenvalues. -/
noncomputable def D : Matrix (Fin 8) (Fin 8) ℂ :=
  Matrix.diagonal (fun k : Fin 8 => (C8eig k : ℂ))

/-- The pointwise eigenvalue relation for the circulant structure. -/
lemma om_key (i k : Fin 8) :
    om ^ ((((i + 1 : Fin 8)) : ℕ) * (k : ℕ)) + om ^ ((((i - 1 : Fin 8)) : ℕ) * (k : ℕ))
      = om ^ ((i : ℕ) * (k : ℕ)) * (C8eig k : ℂ) := by
  have h1 : (((i + 1 : Fin 8)) : ℕ) = ((i : ℕ) + 1) % 8 := by fin_cases i <;> rfl
  have h2 : (((i - 1 : Fin 8)) : ℕ) = ((i : ℕ) + 7) % 8 := by fin_cases i <;> rfl
  have e1 : om ^ ((((i + 1 : Fin 8)) : ℕ) * (k : ℕ))
      = om ^ ((i : ℕ) * (k : ℕ)) * om ^ (k : ℕ) := by
    rw [← pow_add, h1]
    exact om_pow_congr (by simp [add_mul])
  have e2 : om ^ ((((i - 1 : Fin 8)) : ℕ) * (k : ℕ))
      = om ^ ((i : ℕ) * (k : ℕ)) * om ^ (7 * (k : ℕ)) := by
    rw [← pow_add, h2]
    exact om_pow_congr (by simp [add_mul])
  rw [e1, e2, ← mul_add, om_pow_add_inv (k : ℕ)]
  simp [C8eig]

lemma C8adj_row_sum (i k : Fin 8) :
    ∑ j : Fin 8, C8adj i j * P j k = P (i + 1) k + P (i - 1) k := by
  fin_cases i <;>
    simp +decide [C8adj, Fin.sum_univ_eight, Matrix.of_apply,
      show (-1 : Fin 8) = 7 from rfl] <;> exact add_comm _ _

lemma C8adj_mul_P : C8adj * P = P * D := by
  ext i k
  rw [Matrix.mul_apply, C8adj_row_sum, D, Matrix.mul_diagonal, P_apply, P_apply, P_apply]
  exact om_key i k

lemma det_sub_smul (μ : ℂ) :
    (C8adj - μ • (1 : Matrix (Fin 8) (Fin 8) ℂ)).det = ∏ k : Fin 8, ((C8eig k : ℂ) - μ) := by
  have hmul : (C8adj - μ • (1 : Matrix (Fin 8) (Fin 8) ℂ)) * P
      = P * (D - μ • (1 : Matrix (Fin 8) (Fin 8) ℂ)) := by
    rw [sub_mul, mul_sub, C8adj_mul_P, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hD : (D - μ • (1 : Matrix (Fin 8) (Fin 8) ℂ)).det = ∏ k : Fin 8, ((C8eig k : ℂ) - μ) := by
    rw [D, Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub, Matrix.det_diagonal]
  rw [hD] at hdet
  exact mul_right_cancel₀ P_det_ne_zero (by rw [hdet]; ring)

/-- **Hückel theory for the cycle `C₈`**: a complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₈` if and only if `μ = 2 cos (2πk/8)` for some
`k ∈ {0, …, 7}`. -/
theorem huckel_C8 (μ : ℂ) :
    (∃ v : Fin 8 → ℂ, v ≠ 0 ∧ C8adj.mulVec v = μ • v) ↔
      ∃ k : Fin 8, μ = (2 * Real.cos (2 * Real.pi * k / 8) : ℝ) := by
  have hiff : (∃ v : Fin 8 → ℂ, v ≠ 0 ∧ C8adj.mulVec v = μ • v) ↔
      ∃ v : Fin 8 → ℂ, v ≠ 0 ∧ (C8adj - μ • (1 : Matrix (Fin 8) (Fin 8) ℂ)).mulVec v = 0 := by
    refine exists_congr fun v => and_congr_right fun _ => ?_
    rw [Matrix.sub_mulVec, sub_eq_zero]
    simp [Matrix.smul_mulVec, Matrix.one_mulVec]
  rw [hiff, Matrix.exists_mulVec_eq_zero_iff, det_sub_smul, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k, by rw [sub_eq_zero] at hk; rw [← hk]; simp [C8eig]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, by rw [hk]; simp [C8eig]⟩

/-! ### The eight eigenvalues in closed form -/

lemma C8eig_zero : C8eig 0 = 2 := by norm_num [C8eig]

lemma C8eig_one : C8eig 1 = Real.sqrt 2 := by
  rw [C8eig, show (2 * Real.pi * ((1 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi / 4 by norm_num; ring,
    Real.cos_pi_div_four]
  ring

lemma C8eig_two : C8eig 2 = 0 := by
  rw [C8eig, show (2 * Real.pi * ((2 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi / 2 by norm_num; ring,
    Real.cos_pi_div_two]
  ring

lemma C8eig_three : C8eig 3 = -Real.sqrt 2 := by
  rw [C8eig, show (2 * Real.pi * ((3 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi - Real.pi / 4 by
    norm_num; ring, Real.cos_pi_sub, Real.cos_pi_div_four]
  ring

lemma C8eig_four : C8eig 4 = -2 := by
  rw [C8eig, show (2 * Real.pi * ((4 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi by norm_num; ring,
    Real.cos_pi]
  ring

lemma C8eig_five : C8eig 5 = -Real.sqrt 2 := by
  rw [C8eig, show (2 * Real.pi * ((5 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi + Real.pi / 4 by
    norm_num; ring, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_four]
  ring

lemma C8eig_six : C8eig 6 = 0 := by
  rw [C8eig, show (2 * Real.pi * ((6 : Fin 8) : ℕ) / 8 : ℝ) = Real.pi + Real.pi / 2 by
    norm_num; ring, Real.cos_add, Real.cos_pi, Real.sin_pi, Real.cos_pi_div_two]
  ring

lemma C8eig_seven : C8eig 7 = Real.sqrt 2 := by
  rw [C8eig, show (2 * Real.pi * ((7 : Fin 8) : ℕ) / 8 : ℝ) = 2 * Real.pi - Real.pi / 4 by
    norm_num; ring, Real.cos_sub, Real.cos_two_pi, Real.sin_two_pi, Real.cos_pi_div_four]
  ring

lemma Fin8_cases (k : Fin 8) :
    k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 := by
  fin_cases k <;> decide

/-- The Hückel spectrum of `C₈` in closed form: the eigenvalues of the adjacency matrix of
the cycle `C₈` are exactly `2, √2, 0, -√2, -2` (the values `2 cos (2πk/8)`, `k = 0,…,7`). -/
theorem huckel_C8_spectrum (μ : ℂ) :
    (∃ v : Fin 8 → ℂ, v ≠ 0 ∧ C8adj.mulVec v = μ • v) ↔
      μ ∈ ({2, ((Real.sqrt 2 : ℝ) : ℂ), 0, -((Real.sqrt 2 : ℝ) : ℂ), -2} : Set ℂ) := by
  have hval : ∀ j : Fin 8, ((2 * Real.cos (2 * Real.pi * j / 8) : ℝ) : ℂ) = ((C8eig j : ℝ) : ℂ) :=
    fun _ => rfl
  rw [huckel_C8]
  constructor
  · rintro ⟨k, rfl⟩
    rw [hval k]
    rcases Fin8_cases k with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      norm_num [C8eig_zero, C8eig_one, C8eig_two, C8eig_three, C8eig_four, C8eig_five,
        C8eig_six, C8eig_seven, Set.mem_insert_iff]
  · intro h
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
    rcases h with h | h | h | h | h
    · exact ⟨0, by rw [h, hval, C8eig_zero]; norm_num⟩
    · exact ⟨1, by rw [h, hval, C8eig_one]⟩
    · exact ⟨2, by rw [h, hval, C8eig_two]; norm_num⟩
    · exact ⟨3, by rw [h, hval, C8eig_three]; norm_num⟩
    · exact ⟨4, by rw [h, hval, C8eig_four]; norm_num⟩

end Chem

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


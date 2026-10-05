import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

/-- The additive character `ZMod 9 → ℂ`, `a ↦ ω ^ a`. -/
noncomputable def ee (a : ZMod 9) : ℂ := om ^ a.val

/-- Adjacency matrix of the cycle graph `C₉`, on the vertex set `ZMod 9`:
vertices `i` and `j` are adjacent iff `j = i + 1` or `j = i - 1`. -/
def C9adj : Matrix (ZMod 9) (ZMod 9) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The Hückel eigenvalues `2 cos (2 π k / 9)`. -/
noncomputable def eig (k : ZMod 9) : ℂ := 2 * Real.cos (2 * Real.pi * k.val / 9)

/-- The (unnormalised) discrete Fourier matrix, whose columns are the eigenvectors. -/
noncomputable def Pmat : Matrix (ZMod 9) (ZMod 9) ℂ := Matrix.of fun i k => ee (i * k)

/-- The conjugate Fourier matrix. -/
noncomputable def Qmat : Matrix (ZMod 9) (ZMod 9) ℂ := Matrix.of fun i k => ee (-(i * k))

/-! ### Properties of the character `ee` -/

lemma om_primitive : IsPrimitiveRoot om 9 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 9 (by norm_num)

lemma om_pow_nine : om ^ 9 = 1 := om_primitive.pow_eq_one

lemma om_pow_mod (n : ℕ) : om ^ (n % 9) = om ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 9]
  rw [pow_add, pow_mul, om_pow_nine, one_pow, one_mul]

lemma ee_add (a b : ZMod 9) : ee (a + b) = ee a * ee b := by
  simp only [ee, ZMod.val_add, om_pow_mod, pow_add]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_pow (c j : ZMod 9) : ee (c * j) = (ee c) ^ j.val := by
  simp only [ee, ZMod.val_mul, om_pow_mod, pow_mul]

lemma ee_ne_one {c : ZMod 9} (hc : c ≠ 0) : ee c ≠ 1 :=
  om_primitive.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero c).mpr hc) (ZMod.val_lt c)

lemma ee_pow_nine (c : ZMod 9) : (ee c) ^ 9 = 1 := by
  rw [ee, ← pow_mul, mul_comm, pow_mul, om_pow_nine, one_pow]

/-- Orthogonality of characters on `ZMod 9`. -/
lemma sum_ee (c : ZMod 9) : ∑ j : ZMod 9, ee (c * j) = if c = 0 then 9 else 0 := by
  by_cases hc : c = 0
  · simp [hc, ee_zero]
  · simp only [hc, if_false]
    have h : ∑ j : ZMod 9, ee (c * j) = ∑ m ∈ Finset.range 9, (ee c) ^ m := by
      simp only [ee_pow]
      exact Fin.sum_univ_eq_sum_range (fun m => (ee c) ^ m) 9
    rw [h, geom_sum_eq (ee_ne_one hc), ee_pow_nine, sub_self, zero_div]

lemma ee_eq_exp (k : ZMod 9) : ee k = Complex.exp ((2 * Real.pi * k.val / 9 : ℝ) * Complex.I) := by
  rw [ee, om, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- The key trigonometric identity: `ω^k + ω^{-k} = 2 cos (2πk/9)`. -/
lemma ee_add_ee_neg (k : ZMod 9) : ee k + ee (-k) = eig k := by
  have hmul : ee k * ee (-k) = 1 := by rw [← ee_add, add_neg_cancel, ee_zero]
  have hne : ee k ≠ 0 := by
    intro h; rw [h, zero_mul] at hmul; exact zero_ne_one hmul
  have hinv : ee (-k) = (ee k)⁻¹ := by
    field_simp at hmul ⊢
    linear_combination hmul
  rw [hinv, ee_eq_exp, ← Complex.exp_neg]
  rw [show -((2 * Real.pi * (k.val : ℝ) / 9 : ℝ) * Complex.I)
      = ((-(2 * Real.pi * k.val / 9) : ℝ)) * Complex.I by push_cast; ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I, eig]
  push_cast
  rw [Complex.cos_neg, Complex.sin_neg]
  ring

/-! ### The adjacency matrix acts by shifts -/

lemma C9adj_apply (i j : ZMod 9) :
    C9adj i j = (if j = i + 1 then 1 else 0) + (if j = i - 1 then (1 : ℂ) else 0) := by
  have hne : (i + 1 : ZMod 9) ≠ i - 1 := by
    intro h
    have h2 : (2 : ZMod 9) = 0 := by linear_combination h
    exact absurd h2 (by decide)
  by_cases h1 : j = i + 1 <;> by_cases h2 : j = i - 1 <;>
    simp [C9adj, h1, h2] at * <;> tauto

lemma C9adj_mulVec (v : ZMod 9 → ℂ) (i : ZMod 9) :
    (C9adj *ᵥ v) i = v (i + 1) + v (i - 1) := by
  simp [Matrix.mulVec, dotProduct, C9adj_apply, add_mul, Finset.sum_add_distrib, ite_mul,
    Finset.sum_ite_eq']

/-! ### Diagonalisation -/

lemma C9adj_mul_Pmat : C9adj * Pmat = Pmat * Matrix.diagonal eig := by
  ext i k
  have h := C9adj_mulVec (fun j => Pmat j k) i
  simp only [Matrix.mulVec, dotProduct] at h
  rw [Matrix.mul_apply, h, Matrix.mul_diagonal]
  simp only [Pmat, Matrix.of_apply]
  rw [show (i + 1) * k = i * k + k by ring, show (i - 1) * k = i * k + (-k) by ring,
    ee_add, ee_add, ← mul_add, ee_add_ee_neg]

lemma Pmat_mul_Qmat : Pmat * Qmat = (9 : ℂ) • (1 : Matrix (ZMod 9) (ZMod 9) ℂ) := by
  ext i l
  rw [Matrix.mul_apply]
  have hterm : ∀ j : ZMod 9, Pmat i j * Qmat j l = ee ((i - l) * j) := by
    intro j
    simp only [Pmat, Qmat, Matrix.of_apply, ← ee_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), sum_ee]
  by_cases h : i = l
  · simp [h]
  · have hsub : i - l ≠ 0 := sub_ne_zero_of_ne h
    simp [hsub, h]

lemma Pmat_det_ne_zero : Pmat.det ≠ 0 := by
  intro h
  have h2 : (Pmat * Qmat).det = 0 := by rw [Matrix.det_mul, h, zero_mul]
  rw [Pmat_mul_Qmat] at h2
  simp at h2

lemma det_sub_smul (μ : ℂ) :
    (C9adj - μ • (1 : Matrix (ZMod 9) (ZMod 9) ℂ)).det = ∏ k : ZMod 9, (eig k - μ) := by
  have hd : Matrix.diagonal (fun k : ZMod 9 => eig k - μ)
      = Matrix.diagonal eig - μ • (1 : Matrix (ZMod 9) (ZMod 9) ℂ) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  have key : (C9adj - μ • (1 : Matrix (ZMod 9) (ZMod 9) ℂ)) * Pmat
      = Pmat * Matrix.diagonal (fun k : ZMod 9 => eig k - μ) := by
    rw [hd, sub_mul, mul_sub, C9adj_mul_Pmat, Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  exact mul_right_cancel₀ Pmat_det_ne_zero (by rw [hdet]; ring)

/-! ### Main theorem -/

/-- **Hückel theory for the cycle `C₉`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₉` (vertices `ZMod 9`, with `i` adjacent to `i ± 1`)
if and only if `μ = 2 cos (2πk/9)` for some `k ∈ {0, 1, …, 8}`. -/
theorem huckel_C9 (μ : ℂ) :
    (∃ v : ZMod 9 → ℂ, v ≠ 0 ∧ C9adj *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 9 ∧ μ = 2 * Real.cos (2 * Real.pi * k / 9) := by
  have hsmul : ∀ v : ZMod 9 → ℂ, (μ • (1 : Matrix (ZMod 9) (ZMod 9) ℂ)) *ᵥ v = μ • v := by
    intro v; simp [Matrix.smul_mulVec]
  have hiff : (∃ v : ZMod 9 → ℂ, v ≠ 0 ∧ C9adj *ᵥ v = μ • v) ↔
      (∃ v : ZMod 9 → ℂ, v ≠ 0 ∧ (C9adj - μ • (1 : Matrix (ZMod 9) (ZMod 9) ℂ)) *ᵥ v = 0) := by
    constructor
    · rintro ⟨v, hv, hAv⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hAv, hsmul, sub_self]
    · rintro ⟨v, hv, hAv⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hsmul, sub_eq_zero] at hAv
      exact hAv
  rw [hiff, Matrix.exists_mulVec_eq_zero_iff, det_sub_smul, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    refine ⟨k.val, ZMod.val_lt k, ?_⟩
    rw [← sub_eq_zero.mp hk, eig]
  · rintro ⟨k, hk, hμ⟩
    refine ⟨(k : ZMod 9), Finset.mem_univ _, ?_⟩
    rw [sub_eq_zero, eig, ZMod.val_natCast_of_lt hk, hμ]

end

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


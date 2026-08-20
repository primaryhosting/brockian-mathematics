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

/-
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/
noncomputable def zeta12 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 12)

/-- The character `ZMod 12 → ℂ`, `m ↦ ζ^m`. -/
noncomputable def ee (m : ZMod 12) : ℂ := zeta12 ^ m.val

/-- Adjacency matrix of the cycle graph `C₁₂`, indexed by `ZMod 12`. -/
def C12 : Matrix (ZMod 12) (ZMod 12) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- The `k`-th Hückel eigenvalue `2 cos(2πk/12)`. -/
noncomputable def lam (k : ZMod 12) : ℂ := 2 * Real.cos (2 * Real.pi * k.val / 12)

lemma zeta12_primitive : IsPrimitiveRoot zeta12 12 := by
  have h := Complex.isPrimitiveRoot_exp 12 (by norm_num)
  simpa [zeta12] using h

lemma zeta12_pow_twelve : zeta12 ^ 12 = 1 := zeta12_primitive.pow_eq_one

lemma zeta12_pow_mod (m : ℕ) : zeta12 ^ m = zeta12 ^ (m % 12) := by
  conv_lhs => rw [← Nat.div_add_mod m 12]
  rw [pow_add, pow_mul, zeta12_pow_twelve, one_pow, one_mul]

lemma ee_add (a b : ZMod 12) : ee (a + b) = ee a * ee b := by
  rw [ee, ee, ee, ← pow_add, zeta12_pow_mod (a.val + b.val), ZMod.val_add]

lemma ee_zero : ee 0 = 1 := by simp [ee]

lemma ee_ne_zero (m : ZMod 12) : ee m ≠ 0 := by
  simp [ee, zeta12, Complex.exp_ne_zero]

lemma ee_ne_one {m : ZMod 12} (hm : m ≠ 0) : ee m ≠ 1 := by
  intro h
  have h12 : (12 : ℕ) ∣ m.val := (zeta12_primitive.pow_eq_one_iff_dvd m.val).1 h
  have hv : m.val = 0 := Nat.eq_zero_of_dvd_of_lt h12 (ZMod.val_lt m)
  exact hm ((ZMod.val_eq_zero m).1 hv)

lemma ee_natCast_mul (n : ℕ) (m : ZMod 12) : ee ((n : ZMod 12) * m) = ee m ^ n := by
  induction n with
  | zero => simp [ee_zero]
  | succ n ih =>
      have : ((n + 1 : ℕ) : ZMod 12) * m = (n : ZMod 12) * m + m := by push_cast; ring
      rw [this, ee_add, ih, pow_succ]

lemma ee_eq_exp (k : ZMod 12) :
    ee k = Complex.exp (((2 * Real.pi * k.val / 12 : ℝ) : ℂ) * Complex.I) := by
  rw [ee, zeta12, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma ee_add_neg (k : ZMod 12) : ee k + ee (-k) = lam k := by
  have hmul : ee k * ee (-k) = 1 := by rw [← ee_add, add_neg_cancel, ee_zero]
  have hinv : ee (-k) = (ee k)⁻¹ := by
    field_simp [ee_ne_zero k] at hmul ⊢
    linear_combination hmul
  set x : ℝ := 2 * Real.pi * k.val / 12 with hx
  rw [hinv, ee_eq_exp k, ← Complex.exp_neg, lam]
  rw [show -((x : ℂ) * Complex.I) = (-(x:ℂ)) * Complex.I by ring]
  rw [Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg,
    Complex.ofReal_cos]
  push_cast [hx]
  ring

/-- The DFT matrix. -/
noncomputable def F : Matrix (ZMod 12) (ZMod 12) ℂ := Matrix.of fun i k => ee (i * k)

/-- The (unnormalized) inverse DFT matrix. -/
noncomputable def G : Matrix (ZMod 12) (ZMod 12) ℂ := Matrix.of fun k j => ee (-(k * j))

lemma C12_row_sum (i : ZMod 12) (f : ZMod 12 → ℂ) :
    ∑ j : ZMod 12, C12 i j * f j = f (i - 1) + f (i + 1) := by
  have hfilter : (univ.filter fun j : ZMod 12 => i - j = 1 ∨ j - i = 1) = {i - 1, i + 1} := by
    ext j
    simp only [mem_filter, mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
    · rintro (h | h)
      · exact Or.inl (by linear_combination -h)
      · exact Or.inr (by linear_combination h)
  have hne : i - 1 ≠ i + 1 := by
    intro h
    have : (2 : ZMod 12) = 0 := by linear_combination -h
    exact absurd this (by decide)
  calc ∑ j : ZMod 12, C12 i j * f j
      = ∑ j ∈ univ.filter fun j : ZMod 12 => i - j = 1 ∨ j - i = 1, f j := by
        rw [Finset.sum_filter]
        refine Finset.sum_congr rfl fun j _ => ?_
        by_cases h : i - j = 1 ∨ j - i = 1 <;> simp [C12, h]
    _ = f (i - 1) + f (i + 1) := by rw [hfilter, Finset.sum_pair hne]

lemma C12_mul_F : C12 * F = F * Matrix.diagonal lam := by
  ext i k
  rw [Matrix.mul_apply, C12_row_sum i (fun j => F j k), Matrix.mul_diagonal]
  have h1 : (i - 1) * k = i * k + -k := by ring
  have h2 : (i + 1) * k = i * k + k := by ring
  simp only [F, Matrix.of_apply, h1, h2, ee_add]
  rw [← mul_add, add_comm (ee (-k)) (ee k), ee_add_neg]

lemma sum_ee_mul (m : ZMod 12) : ∑ k : ZMod 12, ee (k * m) = if m = 0 then 12 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [ee_zero, ZMod.card]
  · simp only [hm, if_false]
    set S : ℂ := ∑ k : ZMod 12, ee (k * m) with hS
    have hstep : S * ee m = S := by
      have h1 : S * ee m = ∑ k : ZMod 12, ee ((k + 1) * m) := by
        rw [hS, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show (k + 1) * m = k * m + m by ring, ee_add]
      rw [h1]
      exact Equiv.sum_comp (Equiv.addRight (1 : ZMod 12)) (fun k => ee (k * m))
    have : S * (ee m - 1) = 0 := by rw [mul_sub, hstep, mul_one, sub_self]
    rcases mul_eq_zero.1 this with h | h
    · exact h
    · exact absurd (by linear_combination h) (ee_ne_one hm)

lemma F_mul_G : F * G = (12 : ℂ) • (1 : Matrix (ZMod 12) (ZMod 12) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  have : ∀ k : ZMod 12, F i k * G k j = ee (k * (i - j)) := by
    intro k
    simp only [F, G, Matrix.of_apply, ← ee_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun k _ => this k, sum_ee_mul]
  by_cases h : i = j
  · simp [h]
  · have : i - j ≠ 0 := sub_ne_zero.2 h
    simp [this, h]

lemma F_det_ne_zero : F.det ≠ 0 := by
  have h := congrArg Matrix.det F_mul_G
  rw [Matrix.det_mul, Matrix.det_smul, Matrix.det_one, mul_one, ZMod.card] at h
  intro hF
  rw [hF, zero_mul] at h
  exact pow_ne_zero 12 (by norm_num : (12 : ℂ) ≠ 0) h.symm

lemma det_sub_smul (μ : ℂ) :
    (C12 - μ • (1 : Matrix (ZMod 12) (ZMod 12) ℂ)).det = ∏ k : ZMod 12, (lam k - μ) := by
  have hkey : (C12 - μ • (1 : Matrix (ZMod 12) (ZMod 12) ℂ)) * F
      = F * (Matrix.diagonal lam - μ • (1 : Matrix (ZMod 12) (ZMod 12) ℂ)) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, C12_mul_F, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have hdet := congrArg Matrix.det hkey
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hdiag : Matrix.diagonal lam - μ • (1 : Matrix (ZMod 12) (ZMod 12) ℂ)
      = Matrix.diagonal fun k => lam k - μ := by
    rw [Matrix.smul_one_eq_diagonal, ← Matrix.diagonal_sub]
  rw [hdiag, Matrix.det_diagonal] at hdet
  exact mul_right_cancel₀ F_det_ne_zero (hdet.trans (mul_comm _ _))

/-- **Hückel theory for the C₁₂ cycle.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₂` if and only if `μ = 2 cos(2πk/12)` for some
`k = 0, …, 11`. -/
theorem huckel_C12 (μ : ℂ) :
    (∃ v : ZMod 12 → ℂ, v ≠ 0 ∧ C12.mulVec v = μ • v) ↔
      ∃ k : ℕ, k < 12 ∧ μ = 2 * Real.cos (2 * Real.pi * k / 12) := by
  have hEq : (∃ v : ZMod 12 → ℂ, v ≠ 0 ∧ C12.mulVec v = μ • v)
      ↔ ∃ v : ZMod 12 → ℂ, v ≠ 0 ∧
        (C12 - μ • (1 : Matrix (ZMod 12) (ZMod 12) ℂ)).mulVec v = 0 := by
    refine exists_congr fun v => and_congr_right fun _ => ?_
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero]
  rw [hEq, Matrix.exists_mulVec_eq_zero_iff, det_sub_smul, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    exact ⟨k.val, ZMod.val_lt k, by simpa [lam] using (sub_eq_zero.1 hk).symm⟩
  · rintro ⟨n, hn, hμ⟩
    refine ⟨(n : ZMod 12), Finset.mem_univ _, ?_⟩
    have hval : ((n : ZMod 12)).val = n := ZMod.val_natCast_of_lt hn
    rw [lam, hval, ← hμ, sub_self]

/-- The explicit Hückel eigenvectors of `C₁₂`: the discrete Fourier mode
`j ↦ exp(2πi jk/12)` is an eigenvector of the adjacency matrix with eigenvalue
`2 cos(2πk/12)`. -/
theorem huckel_C12_eigenvector (k : ZMod 12) :
    C12.mulVec (fun j => ee (j * k))
      = (2 * Real.cos (2 * Real.pi * k.val / 12) : ℂ) • fun j => ee (j * k) := by
  funext i
  have h := congrFun (congrFun C12_mul_F i) k
  rw [Matrix.mul_apply, Matrix.mul_diagonal] at h
  simpa [Matrix.mulVec, dotProduct, F, lam, mul_comm] using h

end Chem


import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₁`, with vertices indexed by `ZMod 11`:
vertex `i` is adjacent to `i + 1` and `i - 1`. -/
def C11 : Matrix (ZMod 11) (ZMod 11) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The standard additive character `j ↦ exp (2πI j / 11)` of `ZMod 11`. -/
noncomputable def ch : AddChar (ZMod 11) ℂ := ZMod.stdAddChar

/-- The Hückel eigenvalue attached to `k : ZMod 11`, i.e. `2 cos (2πk/11)`. -/
noncomputable def eig (k : ZMod 11) : ℂ := 2 * Real.cos (2 * Real.pi * k.val / 11)

lemma ch_apply (j : ZMod 11) :
    ch j = Complex.exp (2 * Real.pi * Complex.I * j.val / 11) := by
  simpa using ZMod.toCircle_apply (N := 11) j

lemma ch_zero : ch 0 = 1 := AddChar.map_zero_eq_one _

lemma ch_add (a b : ZMod 11) : ch (a + b) = ch a * ch b := AddChar.map_add_eq_mul _ _ _

/-- `ch k + ch (-k) = 2 cos (2πk/11)`. -/
lemma ch_add_ch_neg (k : ZMod 11) : ch k + ch (-k) = eig k := by
  have h1 : ch k = Complex.exp ((↑(2 * Real.pi * k.val / 11) : ℂ) * Complex.I) := by
    rw [ch_apply]
    congr 1
    push_cast
    ring
  have h2 : ch (-k) = Complex.exp (-(↑(2 * Real.pi * k.val / 11) : ℂ) * Complex.I) := by
    have : ch (-k) = (ch k)⁻¹ := AddChar.map_neg_eq_inv _ _
    rw [this, h1, ← Complex.exp_neg]
    congr 1
    ring
  rw [h1, h2, eig, ← Complex.two_cos, Complex.ofReal_cos]

/-- Orthogonality: `∑ i, ch (t * i) = 11` if `t = 0`, and `0` otherwise. -/
lemma sum_ch_mul (t : ZMod 11) :
    ∑ i : ZMod 11, ch (t * i) = if t = 0 then (11 : ℂ) else 0 := by
  split_ifs with h
  · simp [h, Finset.card_univ]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 11 h)

/-- The (unnormalised) discrete Fourier matrix. -/
noncomputable def F : Matrix (ZMod 11) (ZMod 11) ℂ := fun i k => ch (i * k)

/-- The conjugate Fourier matrix. -/
noncomputable def G : Matrix (ZMod 11) (ZMod 11) ℂ := fun k j => ch (-(k * j))

lemma F_mul_G : F * G = (11 : ℂ) • (1 : Matrix (ZMod 11) (ZMod 11) ℂ) := by
  ext i j
  rw [Matrix.mul_apply]
  have : ∀ k : ZMod 11, F i k * G k j = ch ((i - j) * k) := by
    intro k
    rw [F, G, ← ch_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl (fun k _ => this k), sum_ch_mul]
  by_cases h : i = j
  · simp [h]
  · have : i - j ≠ 0 := sub_ne_zero_of_ne h
    simp [this, h]

lemma det_F_ne_zero : F.det ≠ 0 := by
  intro h
  have h2 : F.det * G.det = (11 : ℂ) ^ 11 := by
    rw [← Matrix.det_mul, F_mul_G, Matrix.det_smul, Matrix.det_one, mul_one]
    norm_num
  rw [h, zero_mul] at h2
  norm_num at h2

lemma C11_mulVec (v : ZMod 11 → ℂ) (i : ZMod 11) :
    (C11 *ᵥ v) i = v (i + 1) + v (i - 1) := by
  have hne : ∀ i : ZMod 11, (i + 1 : ZMod 11) ≠ i - 1 := by decide
  have key : ∀ j : ZMod 11,
      C11 i j * v j = (if j = i + 1 then v j else 0) + (if j = i - 1 then v j else 0) := by
    intro j
    by_cases h1 : j = i + 1
    · simp [C11, h1, hne i]
    · by_cases h2 : j = i - 1 <;> simp [C11, h1, h2, Ne.symm (hne i)]
  rw [Matrix.mulVec, dotProduct, Finset.sum_congr rfl (fun j _ => key j),
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i + 1) v,
    Finset.sum_ite_eq' Finset.univ (i - 1) v]
  simp

/-- The columns of `F` are eigenvectors of the adjacency matrix. -/
lemma C11_mul_F : C11 * F = F * Matrix.diagonal eig := by
  ext i k
  rw [Matrix.mul_diagonal]
  have hcol : (C11 * F) i k = (C11 *ᵥ (fun j => F j k)) i := by
    simp [Matrix.mul_apply, Matrix.mulVec, dotProduct]
  rw [hcol, C11_mulVec]
  have e1 : F (i + 1) k = F i k * ch k := by
    rw [F, F, ← ch_add]; congr 1; ring
  have e2 : F (i - 1) k = F i k * ch (-k) := by
    rw [F, F, ← ch_add]; congr 1; ring
  rw [e1, e2, ← mul_add, ch_add_ch_neg]

/-- Explicit eigenvectors: the Bloch wave `j ↦ exp (2πI jk/11)` is an eigenvector of the
adjacency matrix of `C₁₁` with eigenvalue `2 cos (2πk/11)`. -/
lemma C11_mulVec_bloch (k : ZMod 11) :
    C11 *ᵥ (fun j => ch (j * k)) = eig k • (fun j => ch (j * k)) := by
  funext i
  rw [C11_mulVec]
  have e1 : ch ((i + 1) * k) = ch (i * k) * ch k := by rw [← ch_add]; congr 1; ring
  have e2 : ch ((i - 1) * k) = ch (i * k) * ch (-k) := by rw [← ch_add]; congr 1; ring
  rw [e1, e2, ← mul_add, ch_add_ch_neg]
  simp [mul_comm]

/-- The characteristic determinant factors through the Hückel eigenvalues. -/
lemma det_sub_smul (μ : ℂ) :
    (C11 - μ • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)).det = ∏ k : ZMod 11, (eig k - μ) := by
  have hmul : (C11 - μ • 1) * F = F * Matrix.diagonal (fun k => eig k - μ) := by
    have hd : Matrix.diagonal (fun k => eig k - μ)
        = Matrix.diagonal eig - μ • (1 : Matrix (ZMod 11) (ZMod 11) ℂ) := by
      ext i j
      by_cases h : i = j <;> simp [Matrix.diagonal, h]
    rw [hd, Matrix.sub_mul, Matrix.mul_sub, C11_mul_F, Matrix.smul_mul, Matrix.one_mul,
      Matrix.mul_smul, Matrix.mul_one]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have := mul_right_cancel₀ det_F_ne_zero (by rw [hdet]; ring :
    (C11 - μ • 1).det * F.det = (∏ k : ZMod 11, (eig k - μ)) * F.det)
  exact this

/-- **Hückel theory for the cycle `C₁₁`.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₁₁`
(i.e. there is a nonzero vector `v` with `A v = μ v`) if and only if
`μ = 2 cos (2πk/11)` for some `k ∈ {0, 1, …, 10}`. -/
theorem huckel_C11 (μ : ℂ) :
    (∃ v : ZMod 11 → ℂ, v ≠ 0 ∧ C11 *ᵥ v = μ • v) ↔
      ∃ k : ℕ, k < 11 ∧ μ = 2 * Real.cos (2 * Real.pi * k / 11) := by
  have hiff : (∃ v : ZMod 11 → ℂ, v ≠ 0 ∧ C11 *ᵥ v = μ • v) ↔
      (C11 - μ • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, hEq⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hEq, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    · rintro ⟨v, hv, hEq⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hEq
      exact hEq
  rw [hiff, det_sub_smul, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    refine ⟨k.val, ZMod.val_lt k, ?_⟩
    have : μ = eig k := by linear_combination -hk
    rw [this, eig]
  · rintro ⟨k, hk, hμ⟩
    refine ⟨(k : ZMod 11), Finset.mem_univ _, ?_⟩
    have hval : ((k : ZMod 11)).val = k := ZMod.val_natCast_of_lt hk
    rw [eig, hval, hμ, sub_self]

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


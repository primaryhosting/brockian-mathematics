import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset

/-- A primitive 16-th root of unity. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 16)

/-- The adjacency (Hückel) matrix of the cycle graph `C₁₆`, with vertices indexed by
`ZMod 16`: two vertices are adjacent iff their difference is `±1`. -/
def C16 : Matrix (ZMod 16) (ZMod 16) ℂ :=
  fun i j => if i - j = 1 ∨ i - j = -1 then 1 else 0

/-- The claimed Hückel eigenvalues `2·cos(2πk/16)`, `k = 0,…,15`. -/
noncomputable def huckelEigenvalue (k : ZMod 16) : ℂ :=
  2 * (Real.cos (2 * Real.pi * k.val / 16) : ℝ)

/-- The matrix whose `k`-th column is the eigenvector `(ζ^{jk})_j`. -/
noncomputable def Pmat : Matrix (ZMod 16) (ZMod 16) ℂ :=
  Matrix.vandermonde (fun j : ZMod 16 => zeta ^ j.val)

lemma zeta_pow_16 : zeta ^ (16 : ℕ) = 1 := by
  have h := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  have hz : zeta = Complex.exp (2 * Real.pi * Complex.I / ((16 : ℕ) : ℂ)) := by
    norm_num [zeta]
  rw [hz]
  exact h.pow_eq_one

lemma zeta_ne_zero : zeta ≠ 0 := Complex.exp_ne_zero _

lemma zeta_pow_congr {a b : ℕ} (h : a % 16 = b % 16) : zeta ^ a = zeta ^ b := by
  have key : ∀ n : ℕ, zeta ^ n = zeta ^ (n % 16) := by
    intro n
    conv_lhs => rw [← Nat.div_add_mod n 16]
    rw [pow_add, pow_mul, zeta_pow_16, one_pow, one_mul]
  rw [key a, key b, h]

lemma Pmat_apply (i k : ZMod 16) : Pmat i k = zeta ^ (i.val * k.val) := by
  simp [Pmat, Matrix.vandermonde, ← pow_mul]
  rfl

lemma C16_apply_eq (i j : ZMod 16) :
    C16 i j = (if j = i - 1 then (1 : ℂ) else 0) + (if j = i + 1 then (1 : ℂ) else 0) := by
  have hne : (i - 1 : ZMod 16) ≠ i + 1 := by
    intro h
    have h2 : (i - 1) - i = (i + 1) - i := by rw [h]
    have h3 : (-1 : ZMod 16) = 1 := by
      have h5 : (i - 1) - i = (-1 : ZMod 16) := by ring
      have h4 : (i + 1) - i = (1 : ZMod 16) := by ring
      rw [h5, h4] at h2; exact h2
    exact absurd h3 (by decide)
  unfold C16
  by_cases h1 : j = i - 1
  · subst h1
    have e1 : i - (i - 1) = (1 : ZMod 16) := by ring
    rw [e1]
    simp [hne]
  · by_cases h2 : j = i + 1
    · subst h2
      have e2 : i - (i + 1) = (-1 : ZMod 16) := by ring
      rw [e2]
      simp [h1]
    · have hA : i - j ≠ 1 := by
        intro h; exact h1 (by rw [← h]; ring)
      have hB : i - j ≠ -1 := by
        intro h; exact h2 (by
          have h6 : j = i - (i - j) := by ring
          rw [h6, h]; ring)
      simp [hA, hB, h1, h2]

lemma C16_mulVec (v : ZMod 16 → ℂ) (i : ZMod 16) :
    C16.mulVec v i = v (i - 1) + v (i + 1) := by
  simp only [Matrix.mulVec, dotProduct, C16_apply_eq, add_mul, ite_mul, one_mul, zero_mul]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp

lemma zeta_pow_val (k : ZMod 16) :
    zeta ^ k.val = Complex.exp ((2 * Real.pi * k.val / 16 : ℝ) * Complex.I) := by
  rw [zeta, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma huckelEigenvalue_mul (k : ZMod 16) :
    huckelEigenvalue k * zeta ^ k.val = (zeta ^ k.val) ^ 2 + 1 := by
  set t : ℝ := 2 * Real.pi * k.val / 16 with ht
  have hc : zeta ^ k.val = Complex.exp ((t : ℂ) * Complex.I) := zeta_pow_val k
  have h2 : (2 : ℂ) * Complex.cos (t : ℂ)
      = Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-(t : ℂ) * Complex.I) :=
    Complex.two_cos _
  have hinv : Complex.exp (-(t : ℂ) * Complex.I)
      = (Complex.exp ((t : ℂ) * Complex.I))⁻¹ := by
    rw [← Complex.exp_neg]; ring_nf
  have hne : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hlam : huckelEigenvalue k
      = Complex.exp ((t : ℂ) * Complex.I) + (Complex.exp ((t : ℂ) * Complex.I))⁻¹ := by
    rw [huckelEigenvalue, ← ht, Complex.ofReal_cos, h2, hinv]
  rw [hlam, hc]
  field_simp

lemma zeta_succ (i k : ZMod 16) :
    zeta ^ ((i + 1).val * k.val) = zeta ^ (i.val * k.val) * zeta ^ k.val := by
  rw [← pow_add]
  apply zeta_pow_congr
  have hone : (1 : ZMod 16).val = 1 := by decide
  have h1 : (i + 1).val ≡ i.val + 1 [MOD 16] := by
    have h := ZMod.val_add i (1 : ZMod 16)
    rw [hone] at h
    unfold Nat.ModEq
    rw [h, Nat.mod_mod]
  have h2 := h1.mul_right k.val
  unfold Nat.ModEq at h2
  rw [h2]
  ring_nf

lemma zeta_pred (i k : ZMod 16) :
    zeta ^ ((i - 1).val * k.val) * zeta ^ k.val = zeta ^ (i.val * k.val) := by
  rw [← pow_add]
  apply zeta_pow_congr
  have hone : (1 : ZMod 16).val = 1 := by decide
  have hval : ((i - 1) + 1 : ZMod 16) = i := by ring
  have h0 := ZMod.val_add (i - 1) (1 : ZMod 16)
  rw [hval, hone] at h0
  have h1 : (i - 1).val + 1 ≡ i.val [MOD 16] := by
    unfold Nat.ModEq
    rw [← h0]
    exact (Nat.mod_eq_of_lt (ZMod.val_lt i)).symm
  have h2 := h1.mul_right k.val
  unfold Nat.ModEq at h2
  calc ((i - 1).val * k.val + k.val) % 16 = (((i - 1).val + 1) * k.val) % 16 := by ring_nf
    _ = i.val * k.val % 16 := h2

lemma C16_mul_Pmat : C16 * Pmat = Pmat * Matrix.diagonal huckelEigenvalue := by
  ext i k
  rw [Matrix.mul_diagonal]
  have hmul : (C16 * Pmat) i k = C16.mulVec (fun j => Pmat j k) i := rfl
  rw [hmul, C16_mulVec, Pmat_apply, Pmat_apply, Pmat_apply]
  have hz : zeta ^ k.val ≠ 0 := pow_ne_zero _ zeta_ne_zero
  apply mul_right_cancel₀ hz
  rw [add_mul, zeta_pred, zeta_succ, mul_assoc, mul_assoc, huckelEigenvalue_mul]
  ring

lemma Pmat_det_ne_zero : Pmat.det ≠ 0 := by
  rw [Pmat, Matrix.det_vandermonde_ne_zero_iff]
  intro a b hab
  simp only at hab
  have ha : ZMod.val (a : ZMod 16) < 16 := ZMod.val_lt _
  have hb : ZMod.val (b : ZMod 16) < 16 := ZMod.val_lt _
  have h := Complex.isPrimitiveRoot_exp 16 (by norm_num)
  have hz : zeta = Complex.exp (2 * Real.pi * Complex.I / ((16 : ℕ) : ℂ)) := by
    norm_num [zeta]
  rw [hz] at hab
  exact ZMod.val_injective 16 (h.pow_inj ha hb hab)

lemma det_C16_sub (mu : ℂ) :
    (C16 - mu • (1 : Matrix (ZMod 16) (ZMod 16) ℂ)).det
      = ∏ k : ZMod 16, (huckelEigenvalue k - mu) := by
  have hcomm : (C16 - mu • (1 : Matrix (ZMod 16) (ZMod 16) ℂ)) * Pmat
      = Pmat * (Matrix.diagonal huckelEigenvalue - mu • (1 : Matrix (ZMod 16) (ZMod 16) ℂ)) := by
    rw [sub_mul, mul_sub, C16_mul_Pmat, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hdiag : Matrix.diagonal huckelEigenvalue - mu • (1 : Matrix (ZMod 16) (ZMod 16) ℂ)
      = Matrix.diagonal (fun k => huckelEigenvalue k - mu) := by
    rw [Matrix.smul_one_eq_diagonal, Matrix.diagonal_sub]
  have h := congrArg Matrix.det hcomm
  rw [Matrix.det_mul, Matrix.det_mul, hdiag, Matrix.det_diagonal] at h
  apply mul_right_cancel₀ Pmat_det_ne_zero
  rw [h, mul_comm]

/-- **Hückel theory for the C₁₆ cycle.**  A complex number `μ` is an eigenvalue of the
adjacency (Hückel) matrix of the cycle graph `C₁₆` if and only if it is of the form
`2·cos(2πk/16)` for some `k ∈ {0, …, 15}`. -/
theorem huckel_C16 (mu : ℂ) :
    (∃ v : ZMod 16 → ℂ, v ≠ 0 ∧ C16.mulVec v = mu • v) ↔
      ∃ k : ZMod 16, mu = 2 * (Real.cos (2 * Real.pi * k.val / 16) : ℝ) := by
  have hsub : ∀ v : ZMod 16 → ℂ,
      (C16 - mu • (1 : Matrix (ZMod 16) (ZMod 16) ℂ)).mulVec v = C16.mulVec v - mu • v := by
    intro v
    rw [Matrix.sub_mulVec]
    congr 1
    simp [Matrix.smul_mulVec]
  have hiff : (∃ v : ZMod 16 → ℂ, v ≠ 0 ∧ C16.mulVec v = mu • v) ↔
      (C16 - mu • (1 : Matrix (ZMod 16) (ZMod 16) ℂ)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, hvv⟩
      exact ⟨v, hv, by rw [hsub, hvv, sub_self]⟩
    · rintro ⟨v, hv, hvv⟩
      rw [hsub, sub_eq_zero] at hvv
      exact ⟨v, hv, hvv⟩
  rw [hiff, det_C16_sub, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    rw [sub_eq_zero] at hk
    exact ⟨k, by rw [← hk]; rfl⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, by rw [sub_eq_zero, hk]; rfl⟩

/-- The explicit Hückel eigenvectors of `C₁₆`: for each `k`, the vector `j ↦ ζ^(jk)`
(with `ζ = exp(2πi/16)`) is a nonzero eigenvector of the adjacency matrix with
eigenvalue `2·cos(2πk/16)`. -/
theorem huckel_C16_eigenvector (k : ZMod 16) :
    (fun j : ZMod 16 => zeta ^ (j.val * k.val)) ≠ 0 ∧
      C16.mulVec (fun j : ZMod 16 => zeta ^ (j.val * k.val))
        = (2 * (Real.cos (2 * Real.pi * k.val / 16) : ℝ) : ℂ) •
            (fun j : ZMod 16 => zeta ^ (j.val * k.val)) := by
  constructor
  · intro h
    have h0 := congrFun h 0
    simp only [Pi.zero_apply] at h0
    exact pow_ne_zero _ zeta_ne_zero h0
  · funext i
    have hcol := congrFun (congrFun C16_mul_Pmat i) k
    rw [Matrix.mul_diagonal] at hcol
    have hmul : (C16 * Pmat) i k = C16.mulVec (fun j => Pmat j k) i := rfl
    rw [hmul] at hcol
    simp only [Pmat_apply] at hcol
    simpa [huckelEigenvalue, mul_comm] using hcol

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


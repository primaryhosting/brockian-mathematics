import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 10)

/-- The additive character `k ↦ ω^k` of `ZMod 10`. -/
noncomputable def chi (n : ZMod 10) : ℂ := om ^ n.val

/-- Adjacency matrix of the cycle graph `C₁₀`, with vertices indexed by `ZMod 10`:
vertices `i` and `j` are adjacent exactly when `i - j = ±1`. -/
def C10adj : Matrix (ZMod 10) (ZMod 10) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

/-- The Hückel eigenvalues `2 cos (2πk/10)`. -/
noncomputable def C10eigen (k : ZMod 10) : ℂ := 2 * (Real.cos (2 * Real.pi * k.val / 10) : ℝ)

/-- The (unnormalized) discrete Fourier matrix, whose `k`-th column is the eigenvector
`j ↦ ω^{jk}`. -/
noncomputable def C10F : Matrix (ZMod 10) (ZMod 10) ℂ := Matrix.of fun i k => chi (i * k)

/-- The inverse of `C10F`. -/
noncomputable def C10G : Matrix (ZMod 10) (ZMod 10) ℂ :=
  Matrix.of fun k j => chi (-(k * j)) / 10

theorem om_primitive : IsPrimitiveRoot om 10 :=
  Complex.isPrimitiveRoot_exp 10 (by norm_num)

theorem om_pow_ten : om ^ 10 = 1 := om_primitive.pow_eq_one

theorem om_ne_zero : om ≠ 0 := Complex.exp_ne_zero _

theorem chi_ne_zero (k : ZMod 10) : chi k ≠ 0 := pow_ne_zero _ om_ne_zero

theorem chi_natCast (m : ℕ) : chi ((m : ZMod 10)) = om ^ m := by
  rw [chi, ZMod.val_natCast]
  conv_rhs => rw [← Nat.div_add_mod m 10]
  rw [pow_add, pow_mul, om_pow_ten, one_pow, one_mul]

theorem chi_add (a b : ZMod 10) : chi (a + b) = chi a * chi b := by
  have h : chi (a + b) = chi (((a.val + b.val : ℕ) : ZMod 10)) := by congr 1
  rw [h, chi_natCast, pow_add, chi, chi]

theorem chi_zero : chi 0 = 1 := by simp [chi]

theorem chi_neg (k : ZMod 10) : chi (-k) = (chi k)⁻¹ := by
  have h := chi_add k (-k)
  simp [chi_zero] at h
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.symm)

theorem chi_mul_pow (k m : ZMod 10) : chi (k * m) = (chi m) ^ k.val := by
  have h : chi (k * m) = chi (((k.val * m.val : ℕ) : ZMod 10)) := by congr 1
  rw [h, chi_natCast, chi, ← pow_mul, mul_comm]

theorem chi_add_neg (k : ZMod 10) : chi k + chi (-k) = C10eigen k := by
  have hk : chi k = Complex.exp ((2 * Real.pi * k.val / 10 : ℝ) * Complex.I) := by
    rw [chi, om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [C10eigen, chi_neg, hk, Complex.ofReal_cos, Complex.two_cos, ← Complex.exp_neg]
  congr 2
  ring

theorem sum_zmod_range (g : ℕ → ℂ) : ∑ k : ZMod 10, g k.val = ∑ i ∈ Finset.range 10, g i := by
  refine Finset.sum_nbij' (i := fun k => ZMod.val k) (j := fun n => (n : ZMod 10)) ?_ ?_ ?_ ?_ ?_ <;>
    intros <;> simp_all [ZMod.val_lt, Finset.mem_range, ZMod.natCast_val, ZMod.cast_id]

/-- Orthogonality of the characters of `ZMod 10`. -/
theorem sum_chi (m : ZMod 10) : ∑ k : ZMod 10, chi (k * m) = if m = 0 then 10 else 0 := by
  simp only [chi_mul_pow]
  rw [sum_zmod_range (fun n => (chi m) ^ n)]
  by_cases hm : m = 0
  · subst hm
    simp [chi]
  · have hz : chi m ≠ 1 :=
      om_primitive.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero m).mpr hm) (ZMod.val_lt m)
    have h10 : (chi m) ^ 10 = 1 := by
      rw [chi, ← pow_mul, mul_comm, pow_mul, om_pow_ten, one_pow]
    rw [geom_sum_eq hz, h10]
    simp [hm]

theorem adj_mulVec (v : ZMod 10 → ℂ) (i : ZMod 10) :
    (C10adj *ᵥ v) i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 10) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 10) = 0 := by linear_combination -h
    revert h2; decide
  have h : ∀ j : ZMod 10, C10adj i j * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    have h1 : (i - j = 1) ↔ j = i - 1 := by
      constructor
      · intro h; rw [← h]; ring
      · intro h; rw [h]; ring
    have h2 : (j - i = 1) ↔ j = i + 1 := by
      constructor
      · intro h; rw [← h]; ring
      · intro h; rw [h]; ring
    by_cases hA : j = i - 1 <;> by_cases hB : j = i + 1
    · exact absurd (hA.symm.trans hB) hne
    · simp [C10adj, hA, hne]
    · simp [C10adj, hB, hne.symm]
    · simp [C10adj, h1, h2, hA, hB]
  rw [Matrix.mulVec, dotProduct]
  simp only [h, Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ]
  simp

theorem C10F_mul_C10G : C10F * C10G = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 10, C10F i k * C10G k j = chi (k * (i - j)) / 10 := by
    intro k
    rw [C10F, C10G]
    simp only [Matrix.of_apply]
    rw [mul_div_assoc', ← chi_add]
    congr 2
    ring
  simp only [h, ← Finset.sum_div, sum_chi]
  by_cases hij : i = j
  · subst hij
    simp
  · have : i - j ≠ 0 := sub_ne_zero_of_ne hij
    simp [this, hij]

theorem C10F_det_ne_zero : C10F.det ≠ 0 := by
  intro h
  have := congrArg Matrix.det C10F_mul_C10G
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem adj_mul_C10F : C10adj * C10F = C10F * Matrix.diagonal C10eigen := by
  ext i k
  rw [Matrix.mul_diagonal, Matrix.mul_apply]
  have : ∑ j : ZMod 10, C10adj i j * C10F j k
      = (C10adj *ᵥ fun j => C10F j k) i := by
    rw [Matrix.mulVec, dotProduct]
  rw [this, adj_mulVec]
  simp only [C10F, Matrix.of_apply]
  have e1 : (i - 1) * k = i * k + -k := by ring
  have e2 : (i + 1) * k = i * k + k := by ring
  rw [e1, e2, chi_add, chi_add, ← chi_add_neg]
  ring

theorem det_adj_sub (mu : ℂ) :
    (C10adj - mu • (1 : Matrix (ZMod 10) (ZMod 10) ℂ)).det
      = ∏ k : ZMod 10, (C10eigen k - mu) := by
  have key : (C10adj - mu • (1 : Matrix (ZMod 10) (ZMod 10) ℂ)) * C10F
      = C10F * Matrix.diagonal (fun k => C10eigen k - mu) := by
    have hd : Matrix.diagonal (fun k => C10eigen k - mu)
        = Matrix.diagonal C10eigen - mu • (1 : Matrix (ZMod 10) (ZMod 10) ℂ) := by
      ext a b
      rcases eq_or_ne a b with hab | hab
      · simp [hab]
      · simp [hab]
    rw [hd, Matrix.sub_mul, Matrix.mul_sub, adj_mul_C10F, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, Matrix.mul_one]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal] at hdet
  have := mul_right_cancel₀ C10F_det_ne_zero (by rw [hdet]; ring :
    (C10adj - mu • (1 : Matrix (ZMod 10) (ZMod 10) ℂ)).det * C10F.det
      = (∏ k : ZMod 10, (C10eigen k - mu)) * C10F.det)
  exact this

/-- The explicit Hückel molecular orbitals: the vector `j ↦ ω^{jk}` is an eigenvector of the
adjacency matrix of `C₁₀` with eigenvalue `2 cos (2πk/10)`. -/
theorem huckel_C10_eigenvector (k : ZMod 10) :
    C10adj *ᵥ (fun j => chi (j * k)) = C10eigen k • (fun j => chi (j * k)) := by
  funext i
  rw [adj_mulVec]
  have e1 : (i - 1) * k = i * k + -k := by ring
  have e2 : (i + 1) * k = i * k + k := by ring
  simp only [e1, e2, chi_add, Pi.smul_apply, smul_eq_mul]
  rw [← chi_add_neg]
  ring

/-- **Hückel theory for the C₁₀ cycle.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₀` if and only if `μ = 2 cos (2πk/10)` for some
`k ∈ {0,…,9}`. -/
theorem huckel_C10 (mu : ℂ) :
    (∃ v : ZMod 10 → ℂ, v ≠ 0 ∧ C10adj *ᵥ v = mu • v) ↔
      ∃ k : ℕ, k < 10 ∧ mu = 2 * (Real.cos (2 * Real.pi * k / 10) : ℝ) := by
  have hEq : (∃ v : ZMod 10 → ℂ, v ≠ 0 ∧ C10adj *ᵥ v = mu • v) ↔
      (C10adj - mu • (1 : Matrix (ZMod 10) (ZMod 10) ℂ)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, hvv⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hvv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    · rintro ⟨v, hv, hvv⟩
      refine ⟨v, hv, ?_⟩
      have := hvv
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at this
      exact this
  rw [hEq, det_adj_sub, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    refine ⟨k.val, ZMod.val_lt k, ?_⟩
    have : C10eigen k = mu := sub_eq_zero.mp hk
    rw [← this, C10eigen]
  · rintro ⟨n, hn, hmu⟩
    refine ⟨(n : ZMod 10), Finset.mem_univ _, ?_⟩
    rw [sub_eq_zero, C10eigen, ZMod.val_cast_of_lt hn, hmu]

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


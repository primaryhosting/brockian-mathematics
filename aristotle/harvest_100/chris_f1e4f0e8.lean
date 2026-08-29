/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/
noncomputable def zeta5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The character `m ↦ ζ₅ ^ m` of `ZMod 5`. -/
noncomputable def e5 (m : ZMod 5) : ℂ := zeta5 ^ m.val

/-- The adjacency matrix of the cycle graph `C₅`, with vertices indexed by `ZMod 5`:
vertex `i` is adjacent to `i + 1` and `i - 1`. -/
def C5adj : Matrix (ZMod 5) (ZMod 5) ℂ :=
  fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- The `k`-th Hückel eigenvalue of `C₅`, namely `2 cos (2πk/5)`. -/
noncomputable def huckelEigenvalue (k : ZMod 5) : ℂ :=
  2 * Real.cos (2 * Real.pi * k.val / 5)

/-- The adjacency matrix of `C₅` is symmetric. -/
lemma C5adj_isSymm : C5adj.IsSymm := by
  ext i j
  have h : (j = i + 1 ∨ j = i - 1) ↔ (i = j + 1 ∨ i = j - 1) := by
    constructor <;> rintro (h | h) <;> subst h
    · exact Or.inr (by ring)
    · exact Or.inl (by ring)
    · exact Or.inr (by ring)
    · exact Or.inl (by ring)
  simp only [Matrix.transpose_apply, C5adj]
  exact if_congr h.symm rfl rfl

/-! ### Basic facts about `ζ₅` -/

lemma zeta5_pow_five : zeta5 ^ 5 = 1 := by
  rw [zeta5, ← Complex.exp_nat_mul]
  rw [show ((5 : ℕ) : ℂ) * (2 * Real.pi * Complex.I / 5) = 2 * Real.pi * Complex.I by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma zeta5_primitive : IsPrimitiveRoot zeta5 5 := by
  have h := Complex.isPrimitiveRoot_exp 5 (by norm_num)
  simpa [zeta5] using h

lemma zeta5_pow_mod (x : ℕ) : zeta5 ^ (x % 5) = zeta5 ^ x := by
  conv_rhs => rw [← Nat.div_add_mod x 5]
  rw [pow_add, pow_mul, zeta5_pow_five, one_pow, one_mul]

/-! ### Basic facts about the character `e5` -/

lemma e5_zero : e5 0 = 1 := by simp [e5]

lemma e5_add (a b : ZMod 5) : e5 (a + b) = e5 a * e5 b := by
  simp only [e5, ZMod.val_add, zeta5_pow_mod, pow_add]

lemma e5_ne_zero (m : ZMod 5) : e5 m ≠ 0 := by
  have : zeta5 ≠ 0 := by
    simp [zeta5, Complex.exp_ne_zero]
  exact pow_ne_zero _ this

lemma e5_neg (m : ZMod 5) : e5 (-m) = (e5 m)⁻¹ := by
  have h : e5 m * e5 (-m) = 1 := by rw [← e5_add]; simp [e5_zero]
  field_simp [e5_ne_zero m]
  linear_combination h

lemma e5_nat_mul (n : ℕ) (m : ZMod 5) : e5 ((n : ZMod 5) * m) = e5 m ^ n := by
  induction n with
  | zero => simp [e5_zero]
  | succ n ih =>
      have : ((n + 1 : ℕ) : ZMod 5) * m = (n : ZMod 5) * m + m := by push_cast; ring
      rw [this, e5_add, ih, pow_succ]

lemma e5_pow_five (m : ZMod 5) : e5 m ^ 5 = 1 := by
  rw [← e5_nat_mul 5 m, show ((5 : ℕ) : ZMod 5) = 0 from by decide, zero_mul, e5_zero]

lemma e5_ne_one {m : ZMod 5} (hm : m ≠ 0) : e5 m ≠ 1 :=
  zeta5_primitive.pow_ne_one_of_pos_of_lt ((ZMod.val_ne_zero m).mpr hm) (ZMod.val_lt m)

/-- `e5 k + e5 (-k) = 2 cos (2πk/5)`. -/
lemma e5_add_e5_neg (k : ZMod 5) : e5 k + e5 (-k) = huckelEigenvalue k := by
  have hz : e5 k = Complex.exp (((2 * Real.pi * k.val / 5 : ℝ) : ℂ) * Complex.I) := by
    rw [e5, zeta5, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hzn : e5 (-k) = Complex.exp (-((2 * Real.pi * k.val / 5 : ℝ) : ℂ) * Complex.I) := by
    rw [e5_neg, hz, ← Complex.exp_neg]
    congr 1
    ring
  rw [hz, hzn, huckelEigenvalue, Complex.ofReal_cos, ← Complex.two_cos]

/-! ### Orthogonality -/

lemma sum_e5 (m : ZMod 5) : ∑ i : ZMod 5, e5 (i * m) = if m = 0 then 5 else 0 := by
  have huniv : (univ : Finset (ZMod 5)) = {0, 1, 2, 3, 4} := by decide
  have expand : ∑ i : ZMod 5, e5 (i * m)
      = 1 + e5 m + e5 m ^ 2 + e5 m ^ 3 + e5 m ^ 4 := by
    rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
    have h0 : e5 ((0 : ZMod 5) * m) = 1 := by simp [e5_zero]
    have h1 : e5 ((1 : ZMod 5) * m) = e5 m := by simp
    have h2 : e5 ((2 : ZMod 5) * m) = e5 m ^ 2 := by
      have := e5_nat_mul 2 m; norm_num at this; exact this
    have h3 : e5 ((3 : ZMod 5) * m) = e5 m ^ 3 := by
      have := e5_nat_mul 3 m; norm_num at this; exact this
    have h4 : e5 ((4 : ZMod 5) * m) = e5 m ^ 4 := by
      have := e5_nat_mul 4 m; norm_num at this; exact this
    rw [h0, h1, h2, h3, h4]
    ring
  rw [expand]
  by_cases hm : m = 0
  · subst hm
    norm_num [e5_zero]
  · simp only [hm, if_false]
    have h5 : e5 m ^ 5 = 1 := e5_pow_five m
    have hne : e5 m - 1 ≠ 0 := sub_ne_zero.mpr (e5_ne_one hm)
    have key : (e5 m - 1) * (1 + e5 m + e5 m ^ 2 + e5 m ^ 3 + e5 m ^ 4) = 0 := by
      have : (e5 m - 1) * (1 + e5 m + e5 m ^ 2 + e5 m ^ 3 + e5 m ^ 4) = e5 m ^ 5 - 1 := by
        ring
      rw [this, h5, sub_self]
    exact (mul_eq_zero.mp key).resolve_left hne

/-! ### Diagonalization by the discrete Fourier matrix -/

/-- The discrete Fourier matrix. -/
noncomputable def F5 : Matrix (ZMod 5) (ZMod 5) ℂ := fun j k => e5 (j * k)

/-- The inverse (up to normalization) of the discrete Fourier matrix. -/
noncomputable def G5 : Matrix (ZMod 5) (ZMod 5) ℂ := fun j k => (5 : ℂ)⁻¹ * e5 (-(j * k))

lemma F5_mul_G5 : F5 * G5 = 1 := by
  ext i k
  simp only [Matrix.mul_apply, F5, G5, Matrix.one_apply]
  have : ∀ j : ZMod 5, e5 (i * j) * ((5 : ℂ)⁻¹ * e5 (-(j * k)))
      = (5 : ℂ)⁻¹ * e5 (j * (i - k)) := by
    intro j
    rw [show j * (i - k) = i * j + -(j * k) by ring, e5_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => this j), ← Finset.mul_sum, sum_e5]
  by_cases h : i = k
  · subst h; norm_num
  · have : i - k ≠ 0 := sub_ne_zero.mpr h
    simp [this, h]

lemma det_F5_ne_zero : F5.det ≠ 0 := by
  intro h
  have : F5.det * G5.det = 1 := by
    rw [← Matrix.det_mul, F5_mul_G5, Matrix.det_one]
  rw [h, zero_mul] at this
  exact zero_ne_one this

lemma C5adj_mul_F5 :
    C5adj * F5 = F5 * Matrix.diagonal huckelEigenvalue := by
  ext i k
  have hsplit : ∀ j : ZMod 5, C5adj i j * F5 j k
      = (if j = i + 1 then F5 j k else 0) + (if j = i - 1 then F5 j k else 0) := by
    have hne : (i + 1 : ZMod 5) ≠ i - 1 := by
      intro h
      have h2 : (2 : ZMod 5) = 0 := by linear_combination h
      exact absurd h2 (by decide)
    intro j
    by_cases h1 : j = i + 1
    · simp [C5adj, h1, hne]
    · by_cases h2 : j = i - 1
      · simp [C5adj, h2, hne.symm]
      · simp [C5adj, h1, h2]
  rw [Matrix.mul_apply, Finset.sum_congr rfl (fun j _ => hsplit j), Finset.sum_add_distrib,
    Finset.sum_ite_eq' univ (i + 1) (fun j => F5 j k),
    Finset.sum_ite_eq' univ (i - 1) (fun j => F5 j k)]
  simp only [Finset.mem_univ, if_true]
  rw [Matrix.mul_apply, Finset.sum_eq_single k (fun b _ hb => by simp [Matrix.diagonal, hb])
    (by simp)]
  simp only [F5, Matrix.diagonal_apply_eq]
  rw [show (i + 1) * k = i * k + k by ring, show (i - 1) * k = i * k + -k by ring,
    e5_add, e5_add, ← mul_add, e5_add_e5_neg]

/-! ### The characteristic determinant -/

theorem det_C5adj_sub (mu : ℂ) :
    (C5adj - mu • 1).det = ∏ k : ZMod 5, (huckelEigenvalue k - mu) := by
  have key : (C5adj - mu • (1 : Matrix (ZMod 5) (ZMod 5) ℂ)) * F5
      = F5 * (Matrix.diagonal huckelEigenvalue - mu • 1) := by
    rw [Matrix.sub_mul, Matrix.mul_sub, C5adj_mul_F5]
    congr 1
    rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
  have hdet := congrArg Matrix.det key
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hd : (Matrix.diagonal huckelEigenvalue - mu • (1 : Matrix (ZMod 5) (ZMod 5) ℂ))
      = Matrix.diagonal (fun k => huckelEigenvalue k - mu) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.diagonal, h]
  rw [hd, Matrix.det_diagonal] at hdet
  have := mul_right_cancel₀ det_F5_ne_zero (by rw [hdet]; ring :
    (C5adj - mu • (1 : Matrix (ZMod 5) (ZMod 5) ℂ)).det * F5.det
      = (∏ k : ZMod 5, (huckelEigenvalue k - mu)) * F5.det)
  exact this

/-! ### Eigenvectors -/

/-- The `k`-th Hückel eigenvector of `C₅`. -/
noncomputable def huckelEigenvector (k : ZMod 5) : ZMod 5 → ℂ := fun j => e5 (j * k)

theorem C5adj_mulVec_eigenvector (k : ZMod 5) :
    C5adj.mulVec (huckelEigenvector k) = huckelEigenvalue k • huckelEigenvector k := by
  funext i
  have h := congrFun (congrFun C5adj_mul_F5 i) k
  simp only [Matrix.mul_apply] at h
  simp only [Matrix.mulVec, dotProduct, huckelEigenvector, Pi.smul_apply, smul_eq_mul]
  calc ∑ j, C5adj i j * e5 (j * k) = ∑ j, F5 i j * (Matrix.diagonal huckelEigenvalue) j k := h
    _ = huckelEigenvalue k * e5 (i * k) := by
        rw [Finset.sum_eq_single k (fun b _ hb => by simp [Matrix.diagonal_apply_ne _ hb])
          (by simp)]
        simp [F5, mul_comm]

theorem huckelEigenvector_ne_zero (k : ZMod 5) : huckelEigenvector k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [huckelEigenvector, Pi.zero_apply, zero_mul] at h0
  exact e5_ne_zero 0 h0

/-! ### Main theorem -/

/-- **Hückel theory for the cycle `C₅`.** A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₅` if and only if `μ = 2 cos (2πk/5)` for some
`k ∈ {0, 1, 2, 3, 4}`. -/
theorem huckel_C5 (mu : ℂ) :
    (∃ v : ZMod 5 → ℂ, v ≠ 0 ∧ C5adj.mulVec v = mu • v) ↔
      ∃ k : ZMod 5, mu = 2 * Real.cos (2 * Real.pi * k.val / 5) := by
  constructor
  · rintro ⟨v, hv, hvec⟩
    have hdet : (C5adj - mu • (1 : Matrix (ZMod 5) (ZMod 5) ℂ)).det = 0 := by
      rw [← Matrix.exists_mulVec_eq_zero_iff]
      refine ⟨v, hv, ?_⟩
      have hs : (mu • (1 : Matrix (ZMod 5) (ZMod 5) ℂ)).mulVec v = mu • v := by
        ext i
        simp [Matrix.mulVec, dotProduct, Matrix.one_apply, Finset.sum_ite_eq, mul_comm]
      rw [Matrix.sub_mulVec, hs, hvec, sub_self]
    rw [det_C5adj_sub] at hdet
    obtain ⟨k, -, hk⟩ := Finset.prod_eq_zero_iff.mp hdet
    exact ⟨k, by have := sub_eq_zero.mp hk; simpa [huckelEigenvalue] using this.symm⟩
  · rintro ⟨k, rfl⟩
    exact ⟨huckelEigenvector k, huckelEigenvector_ne_zero k, C5adj_mulVec_eigenvector k⟩

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


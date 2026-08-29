/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for the cycle C₁₁

The adjacency eigenvalues of the cycle graph `C₁₁` are exactly `2 cos (2πk/11)`, `k = 0,…,10`.
-/

open Complex Matrix Finset

namespace Chem

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-! ## The cycle graph and its adjacency matrix -/

/-- The cycle graph on 11 vertices, realised on `ZMod 11`: `i ~ j` iff `i - j = ±1`. -/
def C11 : SimpleGraph (ZMod 11) where
  Adj i j := i - j = 1 ∨ j - i = 1
  symm := by intro i j h; tauto
  loopless := ⟨by decide⟩

instance : DecidableRel C11.Adj :=
  fun i j => inferInstanceAs (Decidable (i - j = 1 ∨ j - i = 1))

/-- `C11` is Mathlib's cycle graph on 11 vertices (`ZMod 11` and `Fin 11` are the same type). -/
theorem C11_eq_cycleGraph : C11 = (SimpleGraph.cycleGraph 11 : SimpleGraph (Fin 11)) := by
  ext i j
  rw [SimpleGraph.cycleGraph_adj']
  show (i - j = 1 ∨ j - i = 1) ↔ _
  revert i j
  decide

/-- The adjacency (Hückel) matrix of `C₁₁`. -/
noncomputable def AC11 : Matrix (ZMod 11) (ZMod 11) ℂ := C11.adjMatrix ℂ

lemma C11_adj_iff (i j : ZMod 11) : C11.Adj i j ↔ (j = i - 1 ∨ j = i + 1) := by
  constructor
  · rintro (h | h)
    · left; linear_combination -h
    · right; linear_combination h
  · rintro (h | h)
    · left; linear_combination -h
    · right; linear_combination h

lemma AC11_apply (i j : ZMod 11) :
    AC11 i j = if j = i - 1 ∨ j = i + 1 then 1 else 0 := by
  simp only [AC11, SimpleGraph.adjMatrix_apply, C11_adj_iff]

lemma sub_one_ne_add_one (i : ZMod 11) : i - 1 ≠ i + 1 := by
  intro h
  have h2 : (2 : ZMod 11) = 0 := by linear_combination -h
  revert h2
  decide

lemma AC11_mulVec (v : ZMod 11 → ℂ) (i : ZMod 11) :
    (AC11 *ᵥ v) i = v (i - 1) + v (i + 1) := by
  have h : ∀ j : ZMod 11, AC11 i j * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    rw [AC11_apply]
    by_cases h1 : j = i - 1
    · subst h1; simp [sub_one_ne_add_one i]
    · by_cases h2 : j = i + 1 <;> simp [h1, h2, Ne.symm (sub_one_ne_add_one i)]
  simp only [Matrix.mulVec, dotProduct, h]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i - 1) v,
    Finset.sum_ite_eq' Finset.univ (i + 1) v]
  simp

/-! ## Roots of unity -/

/-- A primitive 11-th root of unity. -/
noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 11)

lemma om_prim : IsPrimitiveRoot om 11 := by
  simpa [om] using Complex.isPrimitiveRoot_exp 11 (by norm_num)

lemma om_ne_one : om ≠ 1 := by
  intro h
  have h2 := om_prim.eq_orderOf
  rw [h, orderOf_one] at h2
  norm_num at h2

/-- The character `n ↦ ω ^ n` of `ZMod 11`. -/
noncomputable def e (n : ZMod 11) : ℂ := om ^ n.val

lemma e_zero : e 0 = 1 := by simp [e]

lemma e_one : e 1 = om := by simp [e, show (1 : ZMod 11).val = 1 from rfl]

lemma om_pow_nat (m : ℕ) : om ^ m = e (m : ZMod 11) := by
  rw [e, ZMod.val_natCast]
  conv_lhs => rw [← Nat.div_add_mod m 11]
  rw [pow_add, pow_mul, om_prim.pow_eq_one, one_pow, one_mul]

lemma e_add (a b : ZMod 11) : e (a + b) = e a * e b := by
  have h : om ^ (a.val + b.val) = e (((a.val + b.val : ℕ) : ZMod 11)) := om_pow_nat _
  rw [pow_add] at h
  simpa [e, ZMod.natCast_val, ZMod.cast_id] using h.symm

lemma e_ne_zero (a : ZMod 11) : e a ≠ 0 := by simp [e, om, Complex.exp_ne_zero]

lemma e_neg (a : ZMod 11) : e (-a) = (e a)⁻¹ := by
  have h : e a * e (-a) = 1 := by rw [← e_add, add_neg_cancel, e_zero]
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h)

/-- The full character sum over `ZMod 11` vanishes. -/
lemma sum_e : ∑ n : ZMod 11, e n = 0 := by
  have key : om * ∑ n : ZMod 11, e n = ∑ n : ZMod 11, e n := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.addLeft (1 : ZMod 11)) _ _
      (fun x => by simp [e_add, e_one])
  have h2 : (om - 1) * ∑ n : ZMod 11, e n = 0 := by linear_combination key
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h) om_ne_one
  · exact h

lemma sum_e_mul {m : ZMod 11} (hm : m ≠ 0) : ∑ l : ZMod 11, e (l * m) = 0 := by
  rw [← sum_e]
  exact Fintype.sum_equiv (Equiv.mulRight₀ m hm) _ _ (fun l => rfl)

/-! ## Diagonalisation by the discrete Fourier transform -/

/-- The `k`-th Hückel eigenvalue, as `ω^k + ω^{-k}`. -/
noncomputable def lam (k : ZMod 11) : ℂ := e k + e (-k)

lemma lam_eq (k : ZMod 11) : lam k = 2 * Real.cos (2 * Real.pi * k.val / 11) := by
  have hk : e k = Complex.exp ((2 * Real.pi * k.val / 11 : ℝ) * Complex.I) := by
    rw [e, om, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hnk : e (-k) = Complex.exp ((-(2 * Real.pi * k.val / 11) : ℝ) * Complex.I) := by
    rw [e_neg, hk, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  rw [lam, hk, hnk, Complex.exp_mul_I, Complex.exp_mul_I]
  push_cast
  simp [Complex.cos_neg, Complex.sin_neg]
  ring

/-- The discrete Fourier matrix; its `k`-th column is the `k`-th eigenvector. -/
noncomputable def F : Matrix (ZMod 11) (ZMod 11) ℂ := fun j k => e (j * k)

/-- The conjugate Fourier matrix. -/
noncomputable def G : Matrix (ZMod 11) (ZMod 11) ℂ := fun j k => e (-(j * k))

/-- Each column of `F` is an eigenvector of the adjacency matrix. -/
lemma AC11_mulVec_col (k : ZMod 11) :
    AC11 *ᵥ (fun j => F j k) = lam k • (fun j => F j k) := by
  funext j
  rw [AC11_mulVec]
  show e ((j - 1) * k) + e ((j + 1) * k) = lam k * e (j * k)
  rw [show (j - 1) * k = j * k + -k by ring, show (j + 1) * k = j * k + k by ring,
    e_add, e_add, lam]
  ring

lemma AC11_mul_F : AC11 * F = F * Matrix.diagonal lam := by
  ext j k
  have h1 : (AC11 * F) j k = (AC11 *ᵥ (fun l => F l k)) j := rfl
  rw [h1, AC11_mulVec_col, Matrix.mul_diagonal]
  simp [mul_comm]

lemma F_mul_G : F * G = (11 : ℂ) • (1 : Matrix (ZMod 11) (ZMod 11) ℂ) := by
  ext j k
  have h : (F * G) j k = ∑ l : ZMod 11, e (l * (j - k)) := by
    simp only [Matrix.mul_apply, F, G]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [← e_add]
    ring_nf
  rw [h]
  by_cases hjk : j = k
  · subst hjk
    simp [e_zero]
  · rw [sum_e_mul (sub_ne_zero.2 hjk)]
    simp [hjk]

/-- The inverse Fourier matrix. -/
noncomputable def Finv : Matrix (ZMod 11) (ZMod 11) ℂ := (11 : ℂ)⁻¹ • G

lemma F_mul_Finv : F * Finv = 1 := by
  rw [Finv, Matrix.mul_smul, F_mul_G, smul_smul]
  norm_num

lemma det_F_mul_det_Finv : F.det * Finv.det = 1 := by
  rw [← Matrix.det_mul, F_mul_Finv, Matrix.det_one]

lemma AC11_sub_smul_one (mu : ℂ) :
    AC11 - mu • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)
      = F * (Matrix.diagonal lam - mu • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)) * Finv := by
  rw [Matrix.mul_sub, Matrix.sub_mul, ← AC11_mul_F, Matrix.mul_assoc,
    F_mul_Finv, Matrix.mul_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, F_mul_Finv]

lemma diagonal_sub_smul_one (mu : ℂ) :
    Matrix.diagonal lam - mu • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)
      = Matrix.diagonal (fun k => lam k - mu) := by
  ext i j
  by_cases h : i = j <;> simp [h]

lemma det_AC11_sub (mu : ℂ) :
    (AC11 - mu • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)).det = ∏ k : ZMod 11, (lam k - mu) := by
  rw [AC11_sub_smul_one, Matrix.det_mul, Matrix.det_mul, diagonal_sub_smul_one,
    Matrix.det_diagonal]
  rw [show F.det * ∏ k : ZMod 11, (lam k - mu) = (∏ k : ZMod 11, (lam k - mu)) * F.det by ring,
    mul_assoc, det_F_mul_det_Finv, mul_one]

/-! ## The Hückel spectrum -/

/-- **Hückel spectrum of the cycle C₁₁.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₁` if and only if `μ = 2 cos (2πk/11)` for some
`k ∈ {0, 1, …, 10}`. -/
theorem huckel_C11 (mu : ℂ) :
    (∃ v : ZMod 11 → ℂ, v ≠ 0 ∧ AC11 *ᵥ v = mu • v) ↔
      ∃ k : Fin 11, mu = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) := by
  have step1 : (∃ v : ZMod 11 → ℂ, v ≠ 0 ∧ AC11 *ᵥ v = mu • v) ↔
      ∃ v : ZMod 11 → ℂ, v ≠ 0 ∧ (AC11 - mu • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)) *ᵥ v = 0 := by
    constructor
    · rintro ⟨v, hv, hAv⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, hAv, Matrix.smul_mulVec, Matrix.one_mulVec, sub_self]
    · rintro ⟨v, hv, hAv⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hAv
      exact hAv
  rw [step1, Matrix.exists_mulVec_eq_zero_iff, det_AC11_sub, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    refine ⟨⟨k.val, ZMod.val_lt k⟩, ?_⟩
    have hmu : mu = lam k := (sub_eq_zero.1 hk).symm
    rw [hmu, lam_eq]
  · rintro ⟨k, hk⟩
    refine ⟨((k : ℕ) : ZMod 11), Finset.mem_univ _, ?_⟩
    rw [sub_eq_zero, lam_eq, ZMod.val_natCast_of_lt k.isLt, hk]

/-- The characteristic polynomial of the adjacency matrix of `C₁₁` splits as
`∏_{k=0}^{10} (X - 2 cos (2πk/11))`; in particular the eigenvalues, with multiplicity,
are exactly the numbers `2 cos (2πk/11)`, `k = 0,…,10`. -/
theorem huckel_C11_charpoly :
    AC11.charpoly =
      ∏ k : ZMod 11,
        (Polynomial.X - Polynomial.C (2 * Real.cos (2 * Real.pi * k.val / 11) : ℂ)) := by
  refine Polynomial.funext (fun t => ?_)
  rw [Matrix.eval_charpoly, Polynomial.eval_prod]
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, ← lam_eq]
  have h1 : (Matrix.scalar (ZMod 11) t - AC11)
      = -(AC11 - t • (1 : Matrix (ZMod 11) (ZMod 11) ℂ)) := by
    ext i j
    by_cases h : i = j <;> simp [Matrix.scalar_apply, h]
  have h2 : ∏ k : ZMod 11, (lam k - t) = ∏ k : ZMod 11, (-(t - lam k)) :=
    Finset.prod_congr rfl (fun k _ => by ring)
  rw [h1, Matrix.det_neg, det_AC11_sub, h2, Finset.prod_neg]
  simp only [Finset.card_univ, ZMod.card]
  ring

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


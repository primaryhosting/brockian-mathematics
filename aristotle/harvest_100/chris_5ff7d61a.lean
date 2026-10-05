import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset SimpleGraph Matrix

namespace Chem

/-! ### Arithmetic in `Fin 14`

`Fin 14` carries the modular `+`, `-`, `*` and `-·` operations used by
`SimpleGraph.cycleGraph_adj`, but no `CommRing` instance is available for the numeral `14`,
so the handful of ring identities we need are checked by decision procedure. -/

section Fin14

lemma fin14_sub_eq_zero_iff (a b : Fin 14) : a - b = 0 ↔ a = b := by decide +revert

lemma fin14_neg_add (a : Fin 14) : -a + a = 0 := by decide +revert

lemma fin14_mul_sub (j k l : Fin 14) : j * k + -(k * l) = k * (j - l) := by decide +revert

lemma fin14_pred_mul (j k : Fin 14) : (j - 1) * k = j * k + -k := by decide +revert

lemma fin14_succ_mul (j k : Fin 14) : (j + 1) * k = j * k + k := by decide +revert

lemma fin14_adj_iff (j l : Fin 14) :
    (j - l = 1 ∨ l - j = 1) ↔ (l = j - 1 ∨ l = j + 1) := by decide +revert

lemma fin14_pred_ne_succ (j : Fin 14) : (j - 1 : Fin 14) ≠ j + 1 := by decide +revert

end Fin14

/-! ### A primitive 14-th root of unity and the associated character -/

/-- A primitive 14-th root of unity. -/
noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 14)

lemma w_primitive : IsPrimitiveRoot w 14 := by
  have h := Complex.isPrimitiveRoot_exp 14 (by norm_num)
  simpa [w] using h

lemma w_pow_14 : w ^ 14 = 1 := w_primitive.pow_eq_one

lemma w_pow_mod (n : ℕ) : w ^ (n % 14) = w ^ n := by
  conv_rhs => rw [← Nat.div_add_mod n 14]
  rw [pow_add, pow_mul, w_pow_14, one_pow, one_mul]

/-- The additive character `k ↦ ω ^ k` of `Fin 14`. -/
noncomputable def zeta (m : Fin 14) : ℂ := w ^ (m : ℕ)

lemma zeta_add (a b : Fin 14) : zeta (a + b) = zeta a * zeta b := by
  simp [zeta, Fin.val_add, w_pow_mod, pow_add]

lemma zeta_zero : zeta 0 = 1 := by simp [zeta]

lemma zeta_mul (a b : Fin 14) : zeta (a * b) = zeta b ^ (a : ℕ) := by
  simp [zeta, Fin.val_mul, w_pow_mod, ← pow_mul, mul_comm]

lemma zeta_pow_14 (m : Fin 14) : zeta m ^ 14 = 1 := by
  rw [zeta, ← pow_mul, mul_comm, pow_mul, w_pow_14, one_pow]

lemma zeta_ne_one {m : Fin 14} (hm : m ≠ 0) : zeta m ≠ 1 := by
  refine w_primitive.pow_ne_one_of_pos_of_lt ?_ m.isLt
  simpa [Fin.val_eq_zero_iff] using hm

lemma sum_zeta (m : Fin 14) : ∑ k : Fin 14, zeta (k * m) = if m = 0 then 14 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [zeta]
  · rw [if_neg hm]
    have hsum : ∑ k : Fin 14, zeta (k * m) = ∑ n ∈ range 14, (zeta m) ^ n := by
      rw [← Fin.sum_univ_eq_sum_range (fun n => (zeta m) ^ n) 14]
      exact Finset.sum_congr rfl fun k _ => zeta_mul k m
    have hmul : (∑ n ∈ range 14, (zeta m) ^ n) * (zeta m - 1) = 0 := by
      rw [geom_sum_mul, zeta_pow_14, sub_self]
    have hne : zeta m - 1 ≠ 0 := sub_ne_zero.mpr (zeta_ne_one hm)
    rw [hsum]
    exact (mul_eq_zero.mp hmul).resolve_right hne

/-! ### The adjacency matrix of `C₁₄` and its diagonalisation -/

/-- The adjacency matrix of the cycle graph `C₁₄`, over `ℂ`. -/
noncomputable def A14 : Matrix (Fin 14) (Fin 14) ℂ := (cycleGraph 14).adjMatrix ℂ

/-- The discrete Fourier matrix. -/
noncomputable def P14 : Matrix (Fin 14) (Fin 14) ℂ := fun j k => zeta (j * k)

/-- The inverse discrete Fourier matrix (up to the factor `14`). -/
noncomputable def Q14 : Matrix (Fin 14) (Fin 14) ℂ := fun k l => (14 : ℂ)⁻¹ * zeta (-(k * l))

/-- The Hückel eigenvalues `2 cos (2πk/14)`. -/
noncomputable def lam (k : Fin 14) : ℂ := 2 * Real.cos (2 * Real.pi * (k : ℕ) / 14)

lemma zeta_add_neg (k : Fin 14) : zeta k + zeta (-k) = lam k := by
  set x : ℝ := 2 * Real.pi * (k : ℕ) / 14 with hx
  have hzk : zeta k = Complex.exp ((x : ℂ) * Complex.I) := by
    rw [zeta, w, ← Complex.exp_nat_mul]
    congr 1
    push_cast [hx]
    ring
  have hprod : zeta (-k) * zeta k = 1 := by
    rw [← zeta_add, fin14_neg_add, zeta_zero]
  have hzmk : zeta (-k) = Complex.exp (-(x : ℂ) * Complex.I) := by
    have h1 : Complex.exp (-(x : ℂ) * Complex.I) * Complex.exp ((x : ℂ) * Complex.I) = 1 := by
      rw [← Complex.exp_add]
      simp
    have hne : Complex.exp ((x : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    rw [hzk] at hprod
    exact mul_right_cancel₀ hne (hprod.trans h1.symm)
  rw [hzk, hzmk, ← Complex.two_cos, lam, Complex.ofReal_cos]

lemma P_mul_Q : P14 * Q14 = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have hstep : ∀ k : Fin 14, P14 j k * Q14 k l = (14 : ℂ)⁻¹ * zeta (k * (j - l)) := by
    intro k
    have hz : zeta (j * k) * zeta (-(k * l)) = zeta (k * (j - l)) := by
      rw [← zeta_add, fin14_mul_sub]
    rw [P14, Q14, show zeta (j * k) * ((14 : ℂ)⁻¹ * zeta (-(k * l)))
        = (14 : ℂ)⁻¹ * (zeta (j * k) * zeta (-(k * l))) by ring, hz]
  rw [Finset.sum_congr rfl fun k _ => hstep k, ← Finset.mul_sum, sum_zeta]
  by_cases h : j = l
  · subst h
    simp
  · have hne : j - l ≠ 0 := fun hc => h ((fin14_sub_eq_zero_iff j l).mp hc)
    rw [if_neg hne, Matrix.one_apply_ne h]
    ring

lemma det_P_ne_zero : P14.det ≠ 0 := by
  intro h
  have hd := congrArg Matrix.det P_mul_Q
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at hd
  exact zero_ne_one hd

lemma A_apply (j l : Fin 14) :
    A14 j l = (if l = j - 1 then 1 else 0) + (if l = j + 1 then 1 else 0) := by
  have hadj : (cycleGraph 14).Adj j l ↔ (l = j - 1 ∨ l = j + 1) :=
    (SimpleGraph.cycleGraph_adj (n := 12)).trans (fin14_adj_iff j l)
  rw [A14, SimpleGraph.adjMatrix_apply]
  by_cases h1 : l = j - 1
  · subst h1
    rw [if_pos (hadj.mpr (Or.inl rfl)), if_pos rfl, if_neg (fin14_pred_ne_succ j)]
    ring
  · by_cases h2 : l = j + 1
    · subst h2
      rw [if_pos (hadj.mpr (Or.inr rfl)), if_neg h1, if_pos rfl]
      ring
    · rw [if_neg (fun h => (hadj.mp h).elim h1 h2), if_neg h1, if_neg h2]
      ring

lemma A_mul_P : A14 * P14 = P14 * Matrix.diagonal lam := by
  ext j k
  rw [Matrix.mul_apply, Matrix.mul_apply]
  have hL : ∑ l : Fin 14, A14 j l * P14 l k = P14 (j - 1) k + P14 (j + 1) k := by
    simp [A_apply, add_mul, ite_mul, Finset.sum_add_distrib]
  have h1 : P14 (j - 1) k = zeta (j * k) * zeta (-k) := by
    rw [P14, fin14_pred_mul, zeta_add]
  have h2 : P14 (j + 1) k = zeta (j * k) * zeta k := by
    rw [P14, fin14_succ_mul, zeta_add]
  have hR : ∑ l : Fin 14, P14 j l * Matrix.diagonal lam l k = P14 j k * lam k := by
    simp [Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq']
  rw [hL, h1, h2, hR, P14, ← zeta_add_neg k]
  ring

lemma det_A_sub (μ : ℂ) : (A14 - μ • (1 : Matrix (Fin 14) (Fin 14) ℂ)).det
    = ∏ k : Fin 14, (lam k - μ) := by
  have hmul : (A14 - μ • 1) * P14 = P14 * (Matrix.diagonal lam - μ • 1) := by
    rw [sub_mul, mul_sub, A_mul_P, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
      Matrix.mul_one]
  have hdet := congrArg Matrix.det hmul
  rw [Matrix.det_mul, Matrix.det_mul] at hdet
  have hdiag : (Matrix.diagonal lam - μ • (1 : Matrix (Fin 14) (Fin 14) ℂ))
      = Matrix.diagonal (fun k => lam k - μ) := by
    ext a b
    by_cases h : a = b <;> simp [h]
  rw [hdiag, Matrix.det_diagonal, mul_comm P14.det] at hdet
  exact mul_right_cancel₀ det_P_ne_zero hdet

/-- **Hückel theory for the cyclic polyene C₁₄.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₄` (the Hückel matrix of C₁₄ in units where `α = 0`,
`β = 1`) if and only if `μ = 2 cos (2πk/14)` for some `k = 0, …, 13`. -/
theorem huckel_C14 (μ : ℂ) :
    (∃ v : Fin 14 → ℂ, v ≠ 0 ∧ ((cycleGraph 14).adjMatrix ℂ).mulVec v = μ • v) ↔
      ∃ k : Fin 14, μ = 2 * Real.cos (2 * Real.pi * (k : ℕ) / 14) := by
  have hiff : (∃ v : Fin 14 → ℂ, v ≠ 0 ∧ ((cycleGraph 14).adjMatrix ℂ).mulVec v = μ • v) ↔
      (A14 - μ • (1 : Matrix (Fin 14) (Fin 14) ℂ)).det = 0 := by
    rw [← Matrix.exists_mulVec_eq_zero_iff]
    constructor
    · rintro ⟨v, hv, hAv⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, A14, hAv, sub_self]
    · rintro ⟨v, hv, hAv⟩
      refine ⟨v, hv, ?_⟩
      rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hAv
      rw [← A14]
      exact sub_eq_zero.mp hAv
  rw [hiff, det_A_sub, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    refine ⟨k, ?_⟩
    have h := sub_eq_zero.mp hk
    rw [lam] at h
    exact h.symm
  · rintro ⟨k, hk⟩
    exact ⟨k, Finset.mem_univ k, by rw [lam, ← hk, sub_self]⟩

/-- The explicit Hückel molecular orbitals of C₁₄: for each `k`, the vector
`j ↦ ω ^ (j * k)` (with `ω = exp (2πi/14)`) is a nonzero eigenvector of the adjacency matrix
of `C₁₄` with eigenvalue `2 cos (2πk/14)`. -/
theorem huckel_C14_eigenvector (k : Fin 14) :
    (fun j : Fin 14 => zeta (j * k)) ≠ 0 ∧
      ((cycleGraph 14).adjMatrix ℂ).mulVec (fun j : Fin 14 => zeta (j * k))
        = (2 * Real.cos (2 * Real.pi * (k : ℕ) / 14) : ℂ) • fun j : Fin 14 => zeta (j * k) := by
  constructor
  · intro h
    have h0 : zeta ((0 : Fin 14) * k) = 0 := congrFun h 0
    rw [zero_mul, zeta_zero] at h0
    exact one_ne_zero h0
  · funext j
    have hcol : ((cycleGraph 14).adjMatrix ℂ).mulVec (fun j : Fin 14 => zeta (j * k)) j
        = (A14 * P14) j k := by
      simp [Matrix.mulVec, Matrix.mul_apply, A14, P14, dotProduct]
    rw [hcol, A_mul_P, Matrix.mul_apply]
    have hR : ∑ l : Fin 14, P14 j l * Matrix.diagonal lam l k = P14 j k * lam k := by
      simp [Matrix.diagonal_apply, mul_ite, Finset.sum_ite_eq']
    rw [hR, P14, lam, Pi.smul_apply, smul_eq_mul, mul_comm]

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


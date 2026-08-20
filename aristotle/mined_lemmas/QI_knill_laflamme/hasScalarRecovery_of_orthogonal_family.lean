/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Statement: A code corrects an error set iff it satisfies the Knill–Laflamme conditions.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- A quantum code, given by the orthogonal projection `P` onto the code subspace. -/
structure IsCodeProj (P : Matrix n n ℂ) : Prop where
  /-- The projection is self-adjoint. -/
  herm : Pᴴ = P
  /-- The projection is idempotent. -/
  idem : P * P = P

/-- The Knill–Laflamme conditions for the code with projection `P` and the error set `E`:
there is a matrix of scalars `c` with `P * (E a)ᴴ * (E b) * P = c a b • P` for all errors
`E a`, `E b`. -/

lemma hasScalarRecovery_of_orthogonal_family (P : Matrix n n ℂ) (hP : IsCodeProj P)
    (E F : ι → Matrix n n ℂ) (d : ι → ℝ) (hd : ∀ k, 0 ≤ d k)
    (horth : ∀ k l, P * (F k)ᴴ * F l * P = (if k = l then ((d k : ℝ) : ℂ) else 0) • P)
    (hE : ∀ a, ∃ t : ι → ℂ, E a * P = ∑ k, t k • (F k * P)) :
    HasScalarRecovery P E := by
  classical
  set Sk : ι → Matrix n n ℂ :=
    fun k => if 0 < d k then (((Real.sqrt (d k))⁻¹ : ℝ) : ℂ) • (P * (F k)ᴴ) else 0 with hSkdef
  set G : ι → Matrix n n ℂ :=
    fun k => if 0 < d k then (((d k)⁻¹ : ℝ) : ℂ) • (F k * P * (F k)ᴴ) else 0 with hGdef
  have hzero : ∀ k, ¬ (0 < d k) → F k * P = 0 := by
    intro k hk
    have hdk : d k = 0 := le_antisymm (not_lt.mp hk) (hd k)
    refine conjTranspose_mul_self_eq_zero.mp ?_
    have h1 := horth k k
    rw [if_pos rfl, hdk] at h1
    rw [conjTranspose_mul, hP.herm]
    simp only [Complex.ofReal_zero, zero_smul] at h1
    rw [← mul_assoc]
    exact h1
  have hSkG : ∀ k, (Sk k)ᴴ * Sk k = G k := by
    intro k
    by_cases hk : 0 < d k
    · simp only [hSkdef, hGdef, if_pos hk, conjTranspose_smul, conjTranspose_mul, hP.herm,
        conjTranspose_conjTranspose, RCLike.star_def, Complex.conj_ofReal, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul]
      rw [← mul_assoc, mul_assoc (F k) P P, hP.idem]
      congr 1
      rw [← Complex.ofReal_mul, ← mul_inv, Real.mul_self_sqrt (le_of_lt hk)]
    · simp [hSkdef, hGdef, if_neg hk]
  have hGmul : ∀ k l, G k * G l = if k = l then G k else 0 := by
    intro k l
    by_cases hk : 0 < d k
    · by_cases hl : 0 < d l
      · have hkey : F k * P * (F k)ᴴ * (F l * P * (F l)ᴴ)
            = F k * (P * (F k)ᴴ * F l * P) * (F l)ᴴ := by noncomm_ring
        simp only [hGdef, if_pos hk, if_pos hl, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
          hkey, horth k l]
        by_cases hkl : k = l
        · subst hkl
          rw [if_pos rfl, if_pos rfl]
          congr 1
          rw [← Complex.ofReal_mul, ← Complex.ofReal_mul]
          congr 1
          field_simp
        · rw [if_neg hkl, if_neg hkl]
          simp
      · simp [hGdef, if_neg hl, if_neg (show ¬ k = l from fun hkl => hl (hkl ▸ hk))]
    · by_cases hkl : k = l
      · subst hkl; simp [hGdef, if_neg hk]
      · simp [hGdef, if_neg hk]
  have hGherm : ∀ k, (G k)ᴴ = G k := by
    intro k
    by_cases hk : 0 < d k
    · simp only [hGdef, if_pos hk, conjTranspose_smul, conjTranspose_mul, hP.herm,
        conjTranspose_conjTranspose, RCLike.star_def, Complex.conj_ofReal]
      rw [← mul_assoc]
    · simp [hGdef, if_neg hk]
  have hSkF : ∀ k l, Sk k * (F l * P)
      = (if k = l then ((Real.sqrt (d k) : ℝ) : ℂ) else 0) • P := by
    intro k l
    by_cases hk : 0 < d k
    · have hkey : P * (F k)ᴴ * (F l * P) = P * (F k)ᴴ * F l * P := by noncomm_ring
      simp only [hSkdef, if_pos hk, Matrix.smul_mul, hkey, horth k l, smul_smul]
      by_cases hkl : k = l
      · rw [if_pos hkl, if_pos hkl]
        congr 1
        rw [← Complex.ofReal_mul]
        congr 1
        rw [inv_mul_eq_div, div_eq_iff (ne_of_gt (Real.sqrt_pos.mpr hk)),
          Real.mul_self_sqrt (le_of_lt hk)]
      · rw [if_neg hkl, if_neg hkl]
        simp
    · have hdk : d k = 0 := le_antisymm (not_lt.mp hk) (hd k)
      simp [hSkdef, if_neg hk, hdk]
  have hGF : ∀ k l, G k * (F l * P) = if k = l then F l * P else 0 := by
    intro k l
    by_cases hk : 0 < d k
    · have hkey : F k * P * (F k)ᴴ * (F l * P) = F k * (P * (F k)ᴴ * F l * P) := by noncomm_ring
      simp only [hGdef, if_pos hk, Matrix.smul_mul, hkey, horth k l]
      by_cases hkl : k = l
      · subst hkl
        rw [if_pos rfl, if_pos rfl, Matrix.mul_smul, smul_smul]
        rw [← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hk)]
        simp
      · rw [if_neg hkl, if_neg hkl]
        simp
    · rw [show G k = 0 by simp [hGdef, if_neg hk], zero_mul]
      by_cases hkl : k = l
      · subst hkl; rw [if_pos rfl, hzero k hk]
      · rw [if_neg hkl]
  set Q : Matrix n n ℂ := ∑ k, G k with hQdef
  have hQF : ∀ l, Q * (F l * P) = F l * P := by
    intro l
    rw [hQdef, Finset.sum_mul]
    rw [Finset.sum_congr rfl fun k _ => hGF k l]
    simp
  have hQQ : Q * Q = Q := by
    rw [hQdef, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.sum_congr rfl fun l _ => hGmul k l]
    simp
  have hQherm : Qᴴ = Q := by
    rw [hQdef, conjTranspose_sum]
    exact Finset.sum_congr rfl fun k _ => hGherm k
  have hQE : ∀ a, Q * (E a * P) = E a * P := by
    intro a
    obtain ⟨t, ht⟩ := hE a
    rw [ht, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Matrix.mul_smul, hQF k]
  refine hasScalarRecovery_of_fintype_family (κ := Option ι) P E
    (fun o => o.elim (1 - Q) Sk) ?_ ?_
  · rw [Fintype.sum_option]
    simp only [Option.elim]
    rw [Finset.sum_congr rfl fun k _ => hSkG k, ← hQdef]
    rw [conjTranspose_sub, conjTranspose_one, hQherm]
    noncomm_ring
    rw [hQQ]
    abel
  · rintro a (_ | k)
    · refine ⟨0, ?_⟩
      simp only [Option.elim]
      rw [sub_mul, sub_mul, one_mul, mul_assoc, hQE a]
      simp
    · obtain ⟨t, ht⟩ := hE a
      refine ⟨t k * ((Real.sqrt (d k) : ℝ) : ℂ), ?_⟩
      simp only [Option.elim]
      rw [mul_assoc, ht, Finset.mul_sum]
      rw [Finset.sum_congr rfl fun l _ => by rw [Matrix.mul_smul, hSkF k l]]
      rw [Finset.sum_eq_single k]
      · rw [if_pos rfl, smul_smul]
      · intro l _ hlk
        rw [if_neg (fun hkl => hlk hkl.symm)]
        simp
      · intro hk
        exact absurd (Finset.mem_univ k) hk

/-- The Knill–Laflamme conditions allow one to build a recovery. -/

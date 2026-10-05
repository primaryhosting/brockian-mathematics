/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Chem

open Finset Complex

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- A primitive 7-th root of unity. -/
noncomputable def zeta7 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)

/-- The additive character `k ↦ ζ₇ ^ k` on `ZMod 7`. -/
noncomputable def chi7 (a : ZMod 7) : ℂ := zeta7 ^ a.val

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`. -/
def C7adj : Matrix (ZMod 7) (ZMod 7) ℂ :=
  fun i j => if i - j = 1 ∨ i - j = -1 then 1 else 0

/-- The eigenvalue attached to `k : ZMod 7`. -/
noncomputable def lam7 (k : ZMod 7) : ℂ := (2 * Real.cos (2 * Real.pi * k.val / 7) : ℝ)

lemma zeta7_prim : IsPrimitiveRoot zeta7 7 := by
  simpa [zeta7] using Complex.isPrimitiveRoot_exp 7 (by norm_num)

lemma zeta7_pow_seven : zeta7 ^ (7 : ℕ) = 1 := zeta7_prim.pow_eq_one

lemma zeta7_pow_natCast (n : ℕ) : zeta7 ^ n = chi7 (n : ZMod 7) := by
  have h : (n : ZMod 7).val = n % 7 := by simp [ZMod.val_natCast]
  rw [chi7, h]
  conv_lhs => rw [← Nat.div_add_mod n 7]
  rw [pow_add, pow_mul, zeta7_pow_seven, one_pow, one_mul]

lemma chi7_add (a b : ZMod 7) : chi7 (a + b) = chi7 a * chi7 b := by
  have hab : a + b = ((a.val + b.val : ℕ) : ZMod 7) := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rfl
  rw [hab, ← zeta7_pow_natCast, pow_add, chi7, chi7]

lemma chi7_zero : chi7 0 = 1 := by simp [chi7]

lemma chi7_mul_neg (a : ZMod 7) : chi7 a * chi7 (-a) = 1 := by
  rw [← chi7_add, add_neg_cancel, chi7_zero]

lemma chi7_ne_zero (a : ZMod 7) : chi7 a ≠ 0 := by
  intro h
  have h1 := chi7_mul_neg a
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

lemma chi7_eq_exp (k : ZMod 7) :
    chi7 k = Complex.exp ((2 * Real.pi * k.val / 7 : ℝ) * Complex.I) := by
  rw [chi7, zeta7, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

lemma chi7_neg_eq_exp (k : ZMod 7) :
    chi7 (-k) = Complex.exp (-((2 * Real.pi * k.val / 7 : ℝ) * Complex.I)) := by
  have h := chi7_mul_neg k
  rw [chi7_eq_exp] at h
  rw [Complex.exp_neg]
  exact eq_inv_of_mul_eq_one_left (by linear_combination h)

lemma chi7_add_chi7_neg (k : ZMod 7) : chi7 k + chi7 (-k) = lam7 k := by
  rw [chi7_eq_exp, chi7_neg_eq_exp, lam7]
  have h := Complex.two_cos ((2 * Real.pi * k.val / 7 : ℝ) : ℂ)
  push_cast at h ⊢
  rw [← neg_mul]
  linear_combination -h

/-- The action of the adjacency matrix on a vector. -/
lemma mulVec_C7adj (v : ZMod 7 → ℂ) (i : ZMod 7) :
    C7adj.mulVec v i = v (i - 1) + v (i + 1) := by
  have hne : (i - 1 : ZMod 7) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 7) = 0 := by linear_combination -h
    exact absurd h2 (by decide)
  have hterm : ∀ j : ZMod 7, C7adj i j * v j
      = (if j = i - 1 then v j else 0) + (if j = i + 1 then v j else 0) := by
    intro j
    simp only [C7adj]
    by_cases h1 : j = i - 1
    · have hij : i - j = 1 := by rw [h1]; ring
      have h2 : j ≠ i + 1 := by rw [h1]; exact hne
      rw [hij, if_pos (Or.inl rfl), if_pos h1, if_neg h2, one_mul, add_zero]
    · by_cases h2 : j = i + 1
      · have hij : i - j = -1 := by rw [h2]; ring
        rw [hij, if_pos (Or.inr rfl), if_neg h1, if_pos h2, one_mul, zero_add]
      · have hz : ¬ (i - j = 1 ∨ i - j = -1) := by
          rintro (h | h)
          · exact h1 (by linear_combination -h)
          · exact h2 (by linear_combination -h)
        rw [if_neg hz, if_neg h1, if_neg h2, zero_mul, add_zero]
  simp only [Matrix.mulVec, dotProduct, hterm]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ (i - 1) v,
    Finset.sum_ite_eq' Finset.univ (i + 1) v]
  simp

/-- The `k`-th Fourier eigenvector. -/
noncomputable def eigvec7 (k : ZMod 7) : ZMod 7 → ℂ := fun j => chi7 (j * k)

lemma eigvec7_ne_zero (k : ZMod 7) : eigvec7 k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [eigvec7, Pi.zero_apply, zero_mul] at h0
  exact chi7_ne_zero 0 h0

/-- Each Fourier vector is an eigenvector with eigenvalue `2cos(2πk/7)`. -/
theorem C7adj_mulVec_eigvec7 (k : ZMod 7) :
    C7adj.mulVec (eigvec7 k) = lam7 k • eigvec7 k := by
  funext i
  rw [mulVec_C7adj]
  simp only [eigvec7, Pi.smul_apply, smul_eq_mul]
  rw [← chi7_add_chi7_neg k]
  have h1 : (i - 1) * k = i * k + (-k) := by ring
  have h2 : (i + 1) * k = i * k + k := by ring
  rw [h1, h2, chi7_add, chi7_add]
  ring

/-- Orthogonality: the sum of the character over `ZMod 7` vanishes. -/
lemma sum_chi7 : ∑ k : ZMod 7, chi7 k = 0 := by
  have hsum : ∑ k : ZMod 7, chi7 k = ∑ n ∈ Finset.range 7, zeta7 ^ n := by
    rw [Finset.sum_nbij' (fun (k : ZMod 7) => k.val) (fun n => (n : ZMod 7))] <;>
      intros <;> simp_all [chi7, ZMod.val_lt, ZMod.val_natCast, Nat.mod_eq_of_lt,
        ZMod.natCast_val, ZMod.cast_id]
  rw [hsum]
  have h1 : zeta7 ≠ 1 := by
    intro h
    have hp := zeta7_prim
    rw [h] at hp
    have := hp.eq_orderOf
    simp at this
  rw [geom_sum_eq h1, zeta7_pow_seven]
  simp

lemma sum_chi7_mul (m : ZMod 7) :
    ∑ k : ZMod 7, chi7 (m * k) = if m = 0 then 7 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [chi7_zero]
  · rw [if_neg hm]
    have hbij : ∑ k : ZMod 7, chi7 (m * k) = ∑ k : ZMod 7, chi7 k :=
      Fintype.sum_bijective (fun k => m * k) (Equiv.mulLeft₀ m hm).bijective _ _ (fun _ => rfl)
    rw [hbij, sum_chi7]

/-- The `k`-th Fourier coefficient of a vector. -/
noncomputable def fcoef (v : ZMod 7 → ℂ) (k : ZMod 7) : ℂ :=
  ∑ l : ZMod 7, v l * chi7 (-(l * k))

/-- Fourier inversion on `ZMod 7`. -/
lemma fourier_inversion (v : ZMod 7 → ℂ) (j : ZMod 7) :
    ∑ k : ZMod 7, fcoef v k * chi7 (j * k) = 7 * v j := by
  have hstep : ∀ k : ZMod 7, fcoef v k * chi7 (j * k)
      = ∑ l : ZMod 7, v l * chi7 ((j - l) * k) := by
    intro k
    rw [fcoef, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hjl : (j - l) * k = -(l * k) + j * k := by ring
    rw [hjl, chi7_add]
    ring
  rw [Finset.sum_congr rfl (fun k _ => hstep k), Finset.sum_comm]
  have hinner : ∀ l : ZMod 7, ∑ k : ZMod 7, v l * chi7 ((j - l) * k)
      = if l = j then 7 * v l else 0 := by
    intro l
    rw [← Finset.mul_sum, sum_chi7_mul]
    by_cases h : l = j
    · subst h
      rw [if_pos (by ring), if_pos rfl]
      ring
    · rw [if_neg (by intro hc; exact h (by linear_combination -hc)), if_neg h]
      ring
  rw [Finset.sum_congr rfl (fun l _ => hinner l)]
  simp

/-- If `v` is an eigenvector for `μ`, each Fourier coefficient satisfies
`(μ - λₖ) cₖ = 0`. -/
lemma fcoef_eigen (μ : ℂ) (v : ZMod 7 → ℂ) (hAv : C7adj.mulVec v = μ • v) (k : ZMod 7) :
    μ * fcoef v k = lam7 k * fcoef v k := by
  have h1 : μ * fcoef v k = ∑ l : ZMod 7, (v (l - 1) + v (l + 1)) * chi7 (-(l * k)) := by
    rw [fcoef, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hl := congrFun hAv l
    rw [mulVec_C7adj] at hl
    simp only [Pi.smul_apply, smul_eq_mul] at hl
    rw [hl]
    ring
  have h2 : ∑ l : ZMod 7, v (l - 1) * chi7 (-(l * k)) = fcoef v k * chi7 (-k) := by
    have e2 : ∑ l : ZMod 7, v (l - 1) * chi7 (-(l * k))
        = ∑ l : ZMod 7, v l * chi7 (-((l + 1) * k)) := by
      refine Fintype.sum_equiv (Equiv.subRight (1 : ZMod 7)) _ _ (fun l => ?_)
      simp only [Equiv.subRight_apply, sub_add_cancel]
    rw [e2, fcoef, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hkk : -((l + 1) * k) = -(l * k) + (-k) := by ring
    rw [hkk, chi7_add]
    ring
  have h3 : ∑ l : ZMod 7, v (l + 1) * chi7 (-(l * k)) = fcoef v k * chi7 k := by
    have e3 : ∑ l : ZMod 7, v (l + 1) * chi7 (-(l * k))
        = ∑ l : ZMod 7, v l * chi7 (-((l - 1) * k)) := by
      refine Fintype.sum_equiv (Equiv.addRight (1 : ZMod 7)) _ _ (fun l => ?_)
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [e3, fcoef, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun l _ => ?_)
    have hkk : -((l - 1) * k) = -(l * k) + k := by ring
    rw [hkk, chi7_add]
    ring
  have h4 : ∑ l : ZMod 7, (v (l - 1) + v (l + 1)) * chi7 (-(l * k))
      = (∑ l : ZMod 7, v (l - 1) * chi7 (-(l * k)))
        + ∑ l : ZMod 7, v (l + 1) * chi7 (-(l * k)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun l _ => by ring)
  rw [h1, h4, h2, h3, ← chi7_add_chi7_neg k]
  ring

/--
**Hückel theory for the cycle `C₇`.**
A complex number `μ` is an eigenvalue of the adjacency matrix of the cycle graph `C₇`
(equivalently, `α + μ·β` is a Hückel energy level of the corresponding annulene) if and
only if `μ = 2·cos(2πk/7)` for some `k ∈ {0, …, 6}`.
-/
theorem huckel_C7 (μ : ℂ) :
    (∃ v : ZMod 7 → ℂ, v ≠ 0 ∧ C7adj.mulVec v = μ • v) ↔
      ∃ k : Fin 7, μ = (2 * Real.cos (2 * Real.pi * k / 7) : ℝ) := by
  constructor
  · rintro ⟨v, hv, hAv⟩
    by_contra hcon
    push_neg at hcon
    have hne : ∀ k : ZMod 7, μ ≠ lam7 k := by
      intro k hk
      exact hcon ⟨k.val, ZMod.val_lt k⟩ (by simpa [lam7] using hk)
    have hc : ∀ k : ZMod 7, fcoef v k = 0 := by
      intro k
      have key := fcoef_eigen μ v hAv k
      have hfac : (μ - lam7 k) * fcoef v k = 0 := by linear_combination key
      rcases mul_eq_zero.mp hfac with h | h
      · exact absurd (sub_eq_zero.mp h) (hne k)
      · exact h
    apply hv
    funext j
    have hinv := fourier_inversion v j
    have hzero : ∀ k ∈ (Finset.univ : Finset (ZMod 7)), fcoef v k * chi7 (j * k) = 0 := by
      intro k _
      rw [hc k, zero_mul]
    rw [Finset.sum_congr rfl hzero, Finset.sum_const_zero] at hinv
    have h7 : (7 : ℂ) * v j = 0 := hinv.symm
    simpa using h7
  · rintro ⟨k, rfl⟩
    refine ⟨eigvec7 ((k : ℕ) : ZMod 7), eigvec7_ne_zero _, ?_⟩
    have hval : (((k : ℕ) : ZMod 7)).val = (k : ℕ) := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt k.isLt]
    rw [C7adj_mulVec_eigvec7]
    congr 1
    simp only [lam7, hval]

end Chem


/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- `g n = exp (2πi n / 19)`, the basic 19-th root of unity raised to `n`. -/

lemma C19_eigenvalue_form {μ : ℂ} {v : ZMod 19 → ℂ} (hv0 : v ≠ 0)
    (hv : C19.mulVec v = μ • v) : ∃ x : ZMod 19, μ = z19 x + z19 (-x) := by
  have hvi : ∀ i : ZMod 19, v (i - 1) + v (i + 1) = μ * v i := by
    intro i
    have h := congrFun hv i
    rwa [C19_mulVec, Pi.smul_apply, smul_eq_mul] at h
  set w : ZMod 19 → ℂ := fun k => ∑ j : ZMod 19, v j * z19 (-(j * k)) with hw
  have claim1 : ∀ k : ZMod 19, μ * w k = (z19 k + z19 (-k)) * w k := by
    intro k
    have e1 : ∑ j : ZMod 19, v (j - 1) * z19 (-(j * k)) = z19 (-k) * w k := by
      rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod 19))
        (fun j : ZMod 19 => v (j - 1) * z19 (-(j * k)))]
      rw [hw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Equiv.coe_addRight, add_sub_cancel_right]
      have hexp : -((j + 1) * k) = -(j * k) + (-k) := by ring
      rw [hexp, z19_add]
      ring
    have e2 : ∑ j : ZMod 19, v (j + 1) * z19 (-(j * k)) = z19 k * w k := by
      rw [← Equiv.sum_comp (Equiv.subRight (1 : ZMod 19))
        (fun j : ZMod 19 => v (j + 1) * z19 (-(j * k)))]
      rw [hw, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [Equiv.subRight_apply, sub_add_cancel]
      have hexp : -((j - 1) * k) = -(j * k) + k := by ring
      rw [hexp, z19_add]
      ring
    calc μ * w k = ∑ j : ZMod 19, (μ * v j) * z19 (-(j * k)) := by
            rw [hw, Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
      _ = ∑ j : ZMod 19, (v (j - 1) * z19 (-(j * k)) + v (j + 1) * z19 (-(j * k))) := by
            refine Finset.sum_congr rfl fun j _ => ?_
            rw [← hvi j]
            ring
      _ = z19 (-k) * w k + z19 k * w k := by rw [Finset.sum_add_distrib, e1, e2]
      _ = (z19 k + z19 (-k)) * w k := by ring
  have claim2 : ∃ k : ZMod 19, w k ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    apply hv0
    funext j
    have inv : ∑ k : ZMod 19, w k * z19 (j * k) = 19 * v j := by
      have hk : ∀ k : ZMod 19, w k * z19 (j * k)
          = ∑ i : ZMod 19, v i * z19 ((j - i) * k) := by
        intro k
        rw [hw, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have hexp : (j - i) * k = -(i * k) + j * k := by ring
        rw [hexp, z19_add]
        ring
      rw [Finset.sum_congr rfl (fun k _ => hk k), Finset.sum_comm]
      have hi : ∀ i : ZMod 19, ∑ k : ZMod 19, v i * z19 ((j - i) * k)
          = if i = j then 19 * v i else 0 := by
        intro i
        rw [← Finset.mul_sum, z19_sum_eq]
        by_cases h : i = j
        · simp [h, mul_comm]
        · have hji : j - i ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
          simp [hji, h]
      rw [Finset.sum_congr rfl (fun i _ => hi i)]
      simp
    have h0 : (19 : ℂ) * v j = 0 := by
      rw [← inv]
      exact Finset.sum_eq_zero fun k _ => by rw [hcon k]; ring
    have hvj : v j = 0 := by
      have h19 : (19 : ℂ) ≠ 0 := by norm_num
      exact (mul_eq_zero.1 h0).resolve_left h19
    simpa using hvj
  obtain ⟨k, hk⟩ := claim2
  exact ⟨k, mul_right_cancel₀ hk (claim1 k)⟩

/-- **Hückel theory for the cycle `C₁₉`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph on 19 vertices if and only if it is one of the
19 numbers `2 cos (2πk/19)`, `k = 0, …, 18`. -/

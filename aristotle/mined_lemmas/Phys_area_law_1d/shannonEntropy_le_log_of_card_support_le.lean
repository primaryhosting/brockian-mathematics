import Mathlib

/-!
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-! ## Shannon entropy of a finite probability vector -/

/-- The Shannon entropy `-∑ pᵢ log pᵢ` of a finite family of reals. -/

theorem shannonEntropy_le_log_of_card_support_le
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (D : ℕ) (hD : (Finset.univ.filter fun i => p i ≠ 0).card ≤ D) :
    shannonEntropy p ≤ Real.log D := by
  classical
  set S : Finset ι := Finset.univ.filter (fun i => p i ≠ 0) with hS
  -- the support is nonempty, since the total mass is `1`
  have hSne : S.Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    have : ∀ i, p i = 0 := by
      intro i
      by_contra hi
      have : i ∈ S := by simp [hS, hi]
      simp [h] at this
    rw [Finset.sum_congr rfl (fun i _ => this i)] at hsum
    simp at hsum
  set n : ℕ := S.card with hn
  have hn0 : 0 < n := Finset.card_pos.mpr hSne
  have hnR : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  -- restrict the entropy sum to the support
  have hrestrict : shannonEntropy p = ∑ i ∈ S, Real.negMulLog (p i) := by
    rw [shannonEntropy, ← Finset.sum_subset (Finset.subset_univ S)]
    intro i _ hi
    have : p i = 0 := by
      by_contra h
      exact hi (by simp [hS, h])
    simp [this, Real.negMulLog]
  -- pointwise bound coming from `log y ≤ y - 1`
  have hpt : ∀ i ∈ S, Real.negMulLog (p i) ≤ p i * Real.log n + (1 / n - p i) := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm (by simpa [hS] using hi))
    have hy : 0 < 1 / ((n : ℝ) * p i) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hy
    have hlogeq : Real.log (1 / ((n : ℝ) * p i)) = -Real.log n - Real.log (p i) := by
      rw [one_div, Real.log_inv, Real.log_mul (ne_of_gt hnR) (ne_of_gt hpi)]
      ring
    have key : -Real.log n - Real.log (p i) ≤ 1 / ((n : ℝ) * p i) - 1 := by
      rw [← hlogeq]; exact hlog
    have hmul := mul_le_mul_of_nonneg_left key (le_of_lt hpi)
    have hsimp : p i * (1 / ((n : ℝ) * p i) - 1) = 1 / n - p i := by
      field_simp
    rw [hsimp] at hmul
    calc Real.negMulLog (p i) = p i * (-Real.log n - Real.log (p i)) + p i * Real.log n := by
          simp [Real.negMulLog]; ring
      _ ≤ (1 / n - p i) + p i * Real.log n := by linarith
      _ = p i * Real.log n + (1 / n - p i) := by ring
  have hsumS : ∑ i ∈ S, p i = 1 := by
    rw [← hsum]
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro i _ hi
    by_contra h
    exact hi (by simp [hS, h])
  have hbound : ∑ i ∈ S, Real.negMulLog (p i)
      ≤ ∑ i ∈ S, (p i * Real.log n + (1 / n - p i)) := Finset.sum_le_sum hpt
  have hrhs : ∑ i ∈ S, (p i * Real.log n + (1 / n - p i)) = Real.log n := by
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, hsumS, one_mul, Finset.sum_sub_distrib,
      hsumS, Finset.sum_const, ← hn, nsmul_eq_mul]
    field_simp
  have hlogle : Real.log n ≤ Real.log D := by
    have hnD : (n : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
    exact Real.log_le_log hnR hnD
  rw [hrestrict]
  linarith [hbound, hrhs.le, hrhs.ge]

/-! ## Von Neumann entropy of a density matrix -/

/-- The von Neumann entropy `-Tr(ρ log ρ)` of a Hermitian matrix, computed from its spectrum
(and set to `0` for non-Hermitian matrices). -/

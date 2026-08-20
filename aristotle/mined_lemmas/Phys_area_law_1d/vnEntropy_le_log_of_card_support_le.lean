/-
# Area Law 1 D
Category: Frontier Phys
Target: Phys.area_law_1d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open Matrix
open scoped ComplexOrder

/-- Von Neumann entropy of a spectrum `p` (a list of eigenvalues of a density matrix). -/

lemma vnEntropy_le_log_of_card_support_le {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ι → ℝ}
    {D : ℕ} (hp : ∀ i, 0 ≤ p i) (hsum : ∑ i, p i = 1)
    (hcard : (Finset.univ.filter fun i => p i ≠ 0).card ≤ D) :
    vnEntropy p ≤ Real.log D := by
  classical
  set S : Finset ι := Finset.univ.filter (fun i => p i ≠ 0) with hSdef
  have hSsum : ∑ i ∈ S, p i = 1 := by
    rw [hSdef, Finset.sum_filter_ne_zero]
    exact hsum
  have hSne : S.Nonempty := by
    rcases Finset.eq_empty_or_nonempty S with h | h
    · rw [h] at hSsum; simp at hSsum
    · exact h
  have hD : 0 < D := lt_of_lt_of_le (Finset.card_pos.mpr hSne) hcard
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hEnt : vnEntropy p = ∑ i ∈ S, -(p i * Real.log (p i)) := by
    rw [vnEntropy]
    refine (Finset.sum_subset (Finset.subset_univ S) ?_).symm
    intro i _ hi
    have hzero : p i = 0 := by
      by_contra h
      exact hi (Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩)
    simp [hzero]
  have key : ∀ i ∈ S, -(p i * Real.log (p i)) ≤ p i * Real.log D + (1 / D - p i) := by
    intro i hi
    have hpi : 0 < p i := lt_of_le_of_ne (hp i) (Ne.symm (Finset.mem_filter.mp hi).2)
    have hx : 0 < 1 / ((D : ℝ) * p i) := by positivity
    have hlog := Real.log_le_sub_one_of_pos hx
    have h1 : Real.log (1 / ((D : ℝ) * p i)) = -(Real.log D + Real.log (p i)) := by
      rw [Real.log_div one_ne_zero (by positivity), Real.log_one,
        Real.log_mul (ne_of_gt hDR) (ne_of_gt hpi)]
      ring
    rw [h1] at hlog
    have hmul := mul_le_mul_of_nonneg_left hlog (le_of_lt hpi)
    have h2 : p i * (1 / ((D : ℝ) * p i) - 1) = 1 / D - p i := by field_simp
    rw [h2] at hmul
    nlinarith [hmul]
  calc vnEntropy p = ∑ i ∈ S, -(p i * Real.log (p i)) := hEnt
    _ ≤ ∑ i ∈ S, (p i * Real.log D + (1 / D - p i)) := Finset.sum_le_sum key
    _ = Real.log D + ((S.card : ℝ) / D - 1) := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, hSsum, one_mul, Finset.sum_sub_distrib,
          hSsum, Finset.sum_const, nsmul_eq_mul]
        ring
    _ ≤ Real.log D := by
        have hle : (S.card : ℝ) / D ≤ 1 := by
          rw [div_le_one hDR]
          exact_mod_cast hcard
        linarith

/-- The spectrum of the reduced density matrix is nonnegative. -/

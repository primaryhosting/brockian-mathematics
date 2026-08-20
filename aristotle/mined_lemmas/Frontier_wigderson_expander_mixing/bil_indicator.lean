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

namespace Frontier

section Mixing

variable {V : Type*} [Fintype V]

/-- The bilinear form associated with a weight matrix `A : V → V → ℝ`. -/

lemma bil_indicator (A : V → V → ℝ) (S T : Finset V) :
    bil A (fun v => if v ∈ S then (1 : ℝ) else 0) (fun v => if v ∈ T then (1 : ℝ) else 0)
      = ∑ u ∈ S, ∑ v ∈ T, A u v := by
  unfold bil
  have inner : ∀ u : V, ∑ v, (if u ∈ S then (1 : ℝ) else 0) * A u v *
      (if v ∈ T then (1 : ℝ) else 0)
      = (if u ∈ S then (1 : ℝ) else 0) * ∑ v ∈ T, A u v := by
    intro u
    rw [Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ T)]
    rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
    have h2 : ∑ v ∈ Finset.univ.filter (fun v => ¬ v ∈ T),
        (if u ∈ S then (1 : ℝ) else 0) * A u v * (if v ∈ T then (1 : ℝ) else 0) = 0 := by
      refine Finset.sum_eq_zero (fun v hv => ?_)
      rw [if_neg (Finset.mem_filter.1 hv).2]; ring
    rw [h2, add_zero]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    rw [if_pos hv]; ring
  rw [Finset.sum_congr rfl (fun u _ => inner u)]
  rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (· ∈ S)]
  rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
  have h3 : ∑ u ∈ Finset.univ.filter (fun u => ¬ u ∈ S),
      (if u ∈ S then (1 : ℝ) else 0) * ∑ v ∈ T, A u v = 0 := by
    refine Finset.sum_eq_zero (fun u hu => ?_)
    rw [if_neg (Finset.mem_filter.1 hu).2]; ring
  rw [h3, add_zero]
  refine Finset.sum_congr rfl (fun u hu => ?_)
  rw [if_pos hu]; ring


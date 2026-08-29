import Mathlib
/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased weight of a subset `T` of the (finite) ground set. -/

noncomputable def wt (p : ℝ) (T : Finset α) : ℝ :=
  p ^ T.card * (1 - p) ^ (Fintype.card α - T.card)

/-- The `p`-biased measure of a family `F` of subsets of the ground set. -/

lemma sum_wt_superset (p : ℝ) (A : Finset α) :
    ∑ T ∈ Finset.univ.filter (fun T : Finset α => A ⊆ T), wt p T = p ^ A.card := by
  classical
  have key : ∑ T ∈ Finset.univ.filter (fun T : Finset α => A ⊆ T), wt p T
      = ∑ U ∈ (Aᶜ).powerset, p ^ A.card * (p ^ U.card * (1 - p) ^ (Aᶜ \ U).card) := by
    refine (Finset.sum_bij' (fun U _ => A ∪ U) (fun T _ => T \ A) ?_ ?_ ?_ ?_ ?_).symm
    · intro U hU
      simp only [Finset.mem_powerset] at hU
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact Finset.subset_union_left
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      simp only [Finset.mem_powerset]
      intro x hx
      simp only [Finset.mem_sdiff] at hx
      simp only [Finset.mem_compl]
      exact hx.2
    · intro U hU
      simp only [Finset.mem_powerset] at hU
      have hdisj : Disjoint A U := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxA hxU
        have := hU hxU
        simp only [Finset.mem_compl] at this
        exact this hxA
      show (A ∪ U) \ A = U
      rw [Finset.union_sdiff_left]
      exact (Finset.sdiff_eq_self_iff_disjoint.mpr hdisj.symm)
    · intro T hT
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hT
      exact Finset.union_sdiff_of_subset hT
    · intro U hU
      simp only [Finset.mem_powerset] at hU
      have hdisj : Disjoint A U := by
        refine Finset.disjoint_left.mpr ?_
        intro x hxA hxU
        have := hU hxU
        simp only [Finset.mem_compl] at this
        exact this hxA
      have hcard : (A ∪ U).card = A.card + U.card := Finset.card_union_of_disjoint hdisj
      have hcompl : (Aᶜ \ U).card = Fintype.card α - (A.card + U.card) := by
        rw [Finset.card_sdiff_of_subset hU, Finset.card_compl]
        have h1 : A.card ≤ Fintype.card α := Finset.card_le_univ A
        have h2 : U.card ≤ (Aᶜ).card := Finset.card_le_card hU
        rw [Finset.card_compl] at h2
        omega
      unfold wt
      rw [hcard, hcompl, pow_add]
      ring
  rw [key, ← Finset.mul_sum]
  have : ∑ U ∈ (Aᶜ).powerset, p ^ U.card * (1 - p) ^ (Aᶜ \ U).card = (p + (1 - p)) ^ (Aᶜ).card := by
    have := Finset.prod_add (fun _ : α => p) (fun _ : α => (1 - p)) (Aᶜ)
    simpa using this.symm
  rw [this]
  simp

end Math2

import Mathlib

/-!
# The `p`-biased measure on subsets of a finite set

Auxiliary measure-theoretic development for `RequestProject.Main` (Kahn–Kalai):
the distribution of the random subset `α_p`, its basic properties, and a block
factorisation which expresses independence over disjoint blocks.
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

set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
namespace Math2

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-! ## The Kahn–Kalai setting

We fix a finite ground set `α`.  For `p ∈ [0,1]`, `α_p` denotes the random subset of `α`
containing each point independently with probability `p`; its distribution is given by the
weights `weight p S = p ^ |S| * (1 - p) ^ (n - |S|)`.

A family `H` of subsets is `q`-*small* if it admits a cover `G` — every member of `H`
contains a member of `G` — of total cost `∑_{g ∈ G} q ^ |g| ≤ 1/2`; the *expectation
threshold* `q(F)` is the largest `q` for which `F` is `q`-small, while the *threshold*
`p_c(F)` is the `p` at which `ℙ(α_p ∈ F) = 1/2`.

### Scope of this file

* `Math2.prob_le_half_of_isSmall` proves, for an **arbitrary** family, the easy direction
  `q(F) ≤ p_c(F)`: if `H` is `q`-small then `ℙ(α_q ∈ ⟨H⟩) ≤ 1/2`.
* `Math2.kahn_kalai` combines this with the converse (Park–Pham) direction for families of
  **pairwise disjoint** sets, for which threshold and expectation threshold are within a
  factor `2`, with no logarithmic loss.
* `Math2.bonferroni_le_prob` and `Math2.half_lt_prob_of_not_isSmall_of_smallOverlap` give the
  same converse direction for arbitrary families whose pairwise overlap term is small.
* The full Park–Pham theorem, `p_c(F) = O(q(F) · log ℓ(F))` for an arbitrary `ℓ`-bounded
  family, is **not** formalised here; in that generality only the easy direction is proved.
-/

/-- The `p`-biased weight of a subset `S` of the finite ground set `α`: the probability
that the random subset `α_p` is exactly `S`. -/

lemma sum_pair_eq (p : ℝ) (H : Finset (Finset α)) :
    ∑ T ∈ H, ∑ T' ∈ H.erase T, p ^ (T ∪ T').card
      = ∑ S : Finset α, weight p S *
          (((H.filter (fun T => T ⊆ S)).card : ℝ) * ((H.filter (fun T => T ⊆ S)).card - 1)) := by
  have hstep : ∀ T ∈ H, ∀ T' ∈ H.erase T,
      p ^ (T ∪ T').card = ∑ S : Finset α, (if T ⊆ S ∧ T' ⊆ S then weight p S else 0) := by
    intro T _ T' _
    rw [pow_card_eq_sum p (T ∪ T')]
    refine Finset.sum_congr rfl fun S _ => ?_
    by_cases hc : T ⊆ S ∧ T' ⊆ S
    · rw [if_pos (Finset.union_subset hc.1 hc.2), if_pos hc]
    · rw [if_neg hc, if_neg]
      intro hsub
      exact hc ⟨Finset.Subset.trans Finset.subset_union_left hsub,
        Finset.Subset.trans Finset.subset_union_right hsub⟩
  rw [Finset.sum_congr rfl fun T hT => Finset.sum_congr rfl fun T' hT' => hstep T hT T' hT']
  have e2 : ∀ T ∈ H,
      (∑ T' ∈ H.erase T, ∑ S : Finset α, (if T ⊆ S ∧ T' ⊆ S then weight p S else 0))
        = ∑ S : Finset α, ∑ T' ∈ H.erase T, (if T ⊆ S ∧ T' ⊆ S then weight p S else 0) :=
    fun T _ => Finset.sum_comm
  rw [Finset.sum_congr rfl e2, Finset.sum_comm]
  refine Finset.sum_congr rfl fun S _ => ?_
  set k : ℕ := (H.filter (fun T => T ⊆ S)).card with hk
  have hinner : ∀ T ∈ H, (∑ T' ∈ H.erase T, (if T ⊆ S ∧ T' ⊆ S then weight p S else 0))
      = (if T ⊆ S then ((k : ℝ) - 1) * weight p S else 0) := by
    intro T hT
    by_cases hTS : T ⊆ S
    · rw [if_pos hTS]
      have : ∀ T' ∈ H.erase T, (if T ⊆ S ∧ T' ⊆ S then weight p S else 0)
          = (if T' ⊆ S then weight p S else 0) := by
        intro T' _
        by_cases hT'S : T' ⊆ S
        · rw [if_pos ⟨hTS, hT'S⟩, if_pos hT'S]
        · rw [if_neg (fun h => hT'S h.2), if_neg hT'S]
      rw [Finset.sum_congr rfl this, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have hcard : ((H.erase T).filter (fun T' => T' ⊆ S)).card = k - 1 := by
        have : (H.erase T).filter (fun T' => T' ⊆ S)
            = (H.filter (fun T' => T' ⊆ S)).erase T := by
          ext T'
          simp only [Finset.mem_filter, Finset.mem_erase]
          tauto
        rw [this, Finset.card_erase_of_mem (Finset.mem_filter.2 ⟨hT, hTS⟩), hk]
      have hkpos : 1 ≤ k := by
        rw [hk]
        exact Finset.card_pos.2 ⟨T, Finset.mem_filter.2 ⟨hT, hTS⟩⟩
      rw [hcard]
      have : ((k - 1 : ℕ) : ℝ) = (k : ℝ) - 1 := by
        have : (1 : ℕ) ≤ k := hkpos
        push_cast [Nat.cast_sub this]
        ring
      rw [this]
    · rw [if_neg hTS]
      refine Finset.sum_eq_zero fun T' _ => ?_
      rw [if_neg (fun h => hTS h.1)]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, ← hk]
  ring

/-- The second Bonferroni inequality for the events "`α_p` contains `T`". -/

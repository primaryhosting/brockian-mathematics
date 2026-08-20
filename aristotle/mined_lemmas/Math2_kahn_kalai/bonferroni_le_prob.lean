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

theorem bonferroni_le_prob {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (H : Finset (Finset α)) :
    (∑ T ∈ H, p ^ T.card) - (∑ T ∈ H, ∑ T' ∈ H.erase T, p ^ (T ∪ T').card) / 2
      ≤ prob p (upClosure H) := by
  rw [sum_pow_card_eq, sum_pair_eq]
  have h2 : ∀ S : Finset α, (S ∈ upClosure H) ↔ 1 ≤ (H.filter (fun T => T ⊆ S)).card := by
    intro S
    simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and,
      Nat.one_le_iff_ne_zero, ne_eq, Finset.card_eq_zero]
    constructor
    · rintro ⟨T, hT, hTS⟩ hempty
      have hmem : T ∈ H.filter (fun T => T ⊆ S) := Finset.mem_filter.2 ⟨hT, hTS⟩
      rw [hempty] at hmem
      exact absurd hmem (Finset.notMem_empty T)
    · intro hne
      obtain ⟨T, hT⟩ := Finset.nonempty_of_ne_empty hne
      exact ⟨T, (Finset.mem_filter.1 hT).1, (Finset.mem_filter.1 hT).2⟩
  have hset : Finset.univ.filter
      (fun S : Finset α => 1 ≤ (H.filter (fun T => T ⊆ S)).card) = upClosure H := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (h2 S).symm
  have hprob : prob p (upClosure H)
      = ∑ S : Finset α, weight p S * (if 1 ≤ (H.filter (fun T => T ⊆ S)).card then 1 else 0) := by
    rw [prob, ← hset, Finset.sum_filter]
    refine Finset.sum_congr rfl fun S _ => ?_
    split_ifs <;> ring
  rw [hprob, Finset.sum_div, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun S _ => ?_
  set k : ℕ := (H.filter (fun T => T ⊆ S)).card with hk
  have hw : 0 ≤ weight p S := weight_nonneg hp0 hp1 S
  have hkey : (k : ℝ) - (k : ℝ) * ((k : ℝ) - 1) / 2 ≤ (if 1 ≤ k then (1 : ℝ) else 0) := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · rw [h0]
      norm_num
    · have h0' : 1 ≤ k := h0
      rw [if_pos h0']
      rcases eq_or_lt_of_le h0' with h1 | h1
      · rw [← h1]
        norm_num
      · have : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast h1
        nlinarith
  calc weight p S * (k : ℝ) - weight p S * ((k : ℝ) * ((k : ℝ) - 1)) / 2
      = weight p S * ((k : ℝ) - (k : ℝ) * ((k : ℝ) - 1) / 2) := by ring
    _ ≤ weight p S * (if 1 ≤ k then (1 : ℝ) else 0) := by
        exact mul_le_mul_of_nonneg_left hkey hw

/-- **Park–Pham direction under a small-overlap hypothesis.**  If `H` has no empty member,
is not `q`-small, and the pairwise overlap sum at `p = min 1 (2q)` is less than `1`, then
`ℙ(α_p ∈ ⟨H⟩) > 1/2`. -/

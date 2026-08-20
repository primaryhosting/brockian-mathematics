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

theorem half_lt_prob_of_not_isSmall_of_smallOverlap {q : ℝ} (hq0 : 0 < q)
    {H : Finset (Finset α)} (hemp : ∅ ∉ H) (h : ¬ IsSmall q H)
    (hover : ∑ T ∈ H, ∑ T' ∈ H.erase T, (min 1 (2 * q)) ^ (T ∪ T').card < 1) :
    1 / 2 < prob (min 1 (2 * q)) (upClosure H) := by
  set p : ℝ := min 1 (2 * q) with hp
  have hp0 : 0 ≤ p := le_min (by norm_num) (by linarith)
  have hp1 : p ≤ 1 := min_le_left _ _
  have hsum : 1 / 2 < ∑ T ∈ H, q ^ T.card := half_lt_sum_of_not_isSmall h
  have hne : H.Nonempty := by
    rcases Finset.eq_empty_or_nonempty H with hh | hh
    · rw [hh] at hsum; simp at hsum; linarith
    · exact hh
  have hcard : ∀ T ∈ H, 1 ≤ T.card := by
    intro T hT
    rcases Nat.eq_zero_or_pos T.card with h0 | h0
    · exact absurd (Finset.card_eq_zero.1 h0 ▸ hT) hemp
    · exact h0
  rcases le_or_gt 1 (2 * q) with hcase | hcase
  · obtain ⟨T₀, hT₀⟩ := hne
    have hp1' : p = 1 := by simp [hp, min_eq_left hcase]
    refine half_lt_prob_of_mem hp0 hp1 hT₀ ?_
    rw [hp1']
    norm_num
  · have hpq : p = 2 * q := by simp [hp, min_eq_right hcase.le]
    have hbig : 1 < ∑ T ∈ H, p ^ T.card := by
      have hterm : ∀ T ∈ H, 2 * q ^ T.card ≤ p ^ T.card := by
        intro T hT
        have h1 : (1 : ℕ) ≤ T.card := hcard T hT
        have h2 : p ^ T.card = 2 ^ T.card * q ^ T.card := by rw [hpq, mul_pow]
        have h3 : (2 : ℝ) ≤ 2 ^ T.card := by
          calc (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
            _ ≤ 2 ^ T.card := pow_le_pow_right₀ (by norm_num) h1
        have h4 : (0 : ℝ) ≤ q ^ T.card := pow_nonneg hq0.le _
        rw [h2]
        nlinarith
      have := Finset.sum_le_sum hterm
      rw [← Finset.mul_sum] at this
      linarith
    have := bonferroni_le_prob hp0 hp1 H
    linarith

/-! ### Main statement -/

/-- **Kahn–Kalai for families of pairwise disjoint sets.**

Let `H` be a family of pairwise disjoint subsets of a finite set, and let `0 < q ≤ 1`.
Then the threshold of the increasing family `⟨H⟩` and the expectation threshold agree up to a
factor `2` (for such families no logarithmic loss is needed):

* if `H` is `q`-small then `ℙ(α_q ∈ ⟨H⟩) ≤ 1/2`, i.e. `q ≤ p_c(⟨H⟩)`;
* if `H` is not `q`-small then `ℙ(α_p ∈ ⟨H⟩) > 1/2` for `p = min 1 (2q)`, i.e.
  `p_c(⟨H⟩) ≤ 2q`.

The first half is the easy direction of the Kahn–Kalai relation and is proved for *arbitrary*
families in `prob_le_half_of_isSmall` (union bound over a cover).  The second half is the
Park–Pham direction; it is proved here for pairwise disjoint families (which includes every
`1`-bounded family, see `half_lt_prob_of_not_isSmall_of_bounded_one`), where the events
"`α_p` contains `T`" are independent and the probability that no member is contained
factorises as `∏_{T ∈ H} (1 - p ^ |T|)`.  For families that are not disjoint but have a
small pairwise overlap term, see `half_lt_prob_of_not_isSmall_of_smallOverlap`. -/

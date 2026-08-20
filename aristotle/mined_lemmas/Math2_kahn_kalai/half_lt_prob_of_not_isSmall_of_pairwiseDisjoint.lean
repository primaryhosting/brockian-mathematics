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

theorem half_lt_prob_of_not_isSmall_of_pairwiseDisjoint {q : ℝ} (hq0 : 0 < q)
    {H : Finset (Finset α)} (hdisj : ((H : Set (Finset α)).Pairwise Disjoint))
    (h : ¬ IsSmall q H) :
    1 / 2 < prob (min 1 (2 * q)) (upClosure H) := by
  set p : ℝ := min 1 (2 * q) with hp
  have hp0 : 0 ≤ p := le_min (by norm_num) (by linarith)
  have hp1 : p ≤ 1 := min_le_left _ _
  have hsum : 1 / 2 < ∑ T ∈ H, q ^ T.card := half_lt_sum_of_not_isSmall h
  by_cases hemp : ∅ ∈ H
  · have huniv : upClosure H = (Finset.univ : Finset (Finset α)) := by
      ext S
      simp only [upClosure, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      exact ⟨∅, hemp, Finset.empty_subset S⟩
    rw [huniv, prob_univ]
    norm_num
  · have hne : H.Nonempty := by
      rcases Finset.eq_empty_or_nonempty H with hh | hh
      · rw [hh] at hsum; simp at hsum; linarith
      · exact hh
    have hcard : ∀ T ∈ H, 1 ≤ T.card := by
      intro T hT
      rcases Nat.eq_zero_or_pos T.card with h0 | h0
      · exact absurd (Finset.card_eq_zero.1 h0 ▸ hT) hemp
      · exact h0
    rw [upClosure_eq_compl]
    have hc := prob_compl (p := p) (Finset.univ.filter (fun S : Finset α => ∀ T ∈ H, ¬ T ⊆ S))
    rw [prob_no_member p hdisj] at hc
    have hlt : ∏ T ∈ H, (1 - p ^ T.card) < 1 / 2 := by
      rcases le_or_gt 1 (2 * q) with hcase | hcase
      · have hp1' : p = 1 := by simp [hp, min_eq_left hcase]
        obtain ⟨T₀, hT₀⟩ := hne
        have hzero : (1 : ℝ) - p ^ T₀.card = 0 := by rw [hp1']; simp
        have : ∏ T ∈ H, (1 - p ^ T.card) = 0 :=
          Finset.prod_eq_zero hT₀ hzero
        rw [this]; norm_num
      · have hpq : p = 2 * q := by simp [hp, min_eq_right hcase.le]
        have hq1 : q < 1 / 2 := by linarith
        -- each factor is bounded by an exponential
        have hstep : ∀ T ∈ H, (1 : ℝ) - p ^ T.card ≤ Real.exp (-(p ^ T.card)) := by
          intro T _
          have := Real.add_one_le_exp (-(p ^ T.card))
          linarith
        have hnonneg : ∀ T ∈ H, (0 : ℝ) ≤ 1 - p ^ T.card := by
          intro T _
          have : p ^ T.card ≤ 1 := pow_le_one₀ hp0 hp1
          linarith
        have hprod : ∏ T ∈ H, (1 - p ^ T.card) ≤ ∏ T ∈ H, Real.exp (-(p ^ T.card)) :=
          Finset.prod_le_prod hnonneg hstep
        have hexp : ∏ T ∈ H, Real.exp (-(p ^ T.card)) = Real.exp (-∑ T ∈ H, p ^ T.card) := by
          rw [← Real.exp_sum]
          congr 1
          rw [← Finset.sum_neg_distrib]
        have hbig : 1 < ∑ T ∈ H, p ^ T.card := by
          have hterm : ∀ T ∈ H, 2 * q ^ T.card ≤ p ^ T.card := by
            intro T hT
            have h1 : (1 : ℕ) ≤ T.card := hcard T hT
            have h2 : p ^ T.card = 2 ^ T.card * q ^ T.card := by
              rw [hpq, mul_pow]
            rw [h2]
            have h3 : (2 : ℝ) ≤ 2 ^ T.card := by
              calc (2 : ℝ) = 2 ^ (1 : ℕ) := by norm_num
                _ ≤ 2 ^ T.card := by
                    exact pow_le_pow_right₀ (by norm_num) h1
            have h4 : (0 : ℝ) ≤ q ^ T.card := pow_nonneg hq0.le _
            nlinarith
          have := Finset.sum_le_sum hterm
          rw [← Finset.mul_sum] at this
          linarith
        have hexplt : Real.exp (-∑ T ∈ H, p ^ T.card) < 1 / 2 := by
          have h6 : Real.exp (-∑ T ∈ H, p ^ T.card) < Real.exp (-1) :=
            Real.exp_lt_exp.2 (by linarith)
          have h7 : Real.exp (-1 : ℝ) < 1 / 2 := by
            have he : (2 : ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
            have hpos : (0 : ℝ) < Real.exp 1 := Real.exp_pos 1
            rw [Real.exp_neg, inv_lt_iff_one_lt_mul₀ hpos]
            linarith
          linarith
        rw [hexp] at hprod
        linarith
    linarith

/-! ### The hard direction for `1`-bounded families

A `1`-bounded family (all members of size at most one) is automatically pairwise disjoint,
so the previous theorem applies. -/

omit [Fintype α] [DecidableEq α] in

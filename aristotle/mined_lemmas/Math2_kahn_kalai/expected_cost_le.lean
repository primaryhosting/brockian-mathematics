/-
Minimum fragments (Park-Pham) and the key lemma: the cover built from the large
minimum fragments has small expected cost.
-/
import RequestProject.Basic

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-! ### Minimum fragments -/

/-- The candidate fragments of `S` relative to `W`: the sets `S' \ W` for edges `S'` of `H`
contained in `W ∪ S`. -/

lemma expected_cost_le {H : Finset (Finset α)} {m : ℕ}
    (hH : ∀ S ∈ H, S.card ≤ m) {p r c : ℝ} (hp : 0 < p) (hc : 1 ≤ c)
    (hr : r = c ^ 2 * p) (hr1 : r ≤ 1) :
    ∑ W : Finset α, wt r W * cost p (Ufam H W m) ≤ (2 / c) ^ m := by
  have hc0 : (0:ℝ) < c := lt_of_lt_of_le zero_lt_one hc
  have hr0 : 0 < r := by rw [hr]; positivity
  have hpr : p / r = (1 / c ^ 2) := by
    rw [hr]; field_simp
  classical
  set Pairs : Finset (Finset α × Finset α) :=
    Finset.univ.filter (fun q => q.2 ∈ Ufam H q.1 m) with hPairs
  set φ : Finset α × Finset α → Finset α × Finset α := fun q => (q.1 ∪ q.2, q.2) with hφ
  set Target : Finset (Finset α × Finset α) :=
    Finset.univ.filter (fun q => q.2 ⊆ pick H q.1 ∧ m ≤ 2 * q.2.card) with hTarget
  have hPairsSum : ∀ g : Finset α × Finset α → ℝ,
      ∑ q ∈ Pairs, g q
        = ∑ W : Finset α, ∑ U : Finset α, if U ∈ Ufam H W m then g (W, U) else 0 := by
    intro g
    rw [hPairs, Finset.sum_filter, Fintype.sum_prod_type]
  -- Step 1: rewrite the left-hand side as a sum over pairs
  have step1 : ∑ W : Finset α, wt r W * cost p (Ufam H W m)
      = ∑ q ∈ Pairs, wt r q.1 * p ^ q.2.card := by
    rw [hPairsSum (fun q => wt r q.1 * p ^ q.2.card)]
    refine Finset.sum_congr rfl ?_
    intro W _
    rw [cost, Finset.mul_sum, sum_finset_as_ite (Ufam H W m) (fun U => wt r W * p ^ U.card)]
  -- Step 2: pointwise reweighting
  have step2 : ∑ q ∈ Pairs, wt r q.1 * p ^ q.2.card
      ≤ ∑ q ∈ Pairs, wt r (q.1 ∪ q.2) * (p / r) ^ q.2.card := by
    refine Finset.sum_le_sum ?_
    intro q hq
    rw [hPairs, Finset.mem_filter] at hq
    exact wt_union_bound hr0 hr1 (Ufam_disjoint hq.2) (le_of_lt hp)
  -- Step 3: reindex by `Z = W ∪ U`
  have hinj : Set.InjOn φ ↑Pairs := by
    intro q1 hq1 q2 hq2 hEq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, hPairs] at hq1 hq2
    simp only [hφ, Prod.mk.injEq] at hEq
    obtain ⟨h2, h1⟩ := hEq
    have d1 : Disjoint q1.1 q1.2 := Ufam_disjoint hq1.2
    have d2 : Disjoint q2.1 q2.2 := Ufam_disjoint hq2.2
    have hfst : q1.1 = q2.1 := by
      have e1 : (q1.1 ∪ q1.2) \ q1.2 = q1.1 := by
        rw [Finset.union_sdiff_right]
        exact Finset.sdiff_eq_self_of_disjoint d1
      have e2 : (q2.1 ∪ q2.2) \ q2.2 = q2.1 := by
        rw [Finset.union_sdiff_right]
        exact Finset.sdiff_eq_self_of_disjoint d2
      have e3 : q1.1 = (q2.1 ∪ q2.2) \ q2.2 := by
        rw [← h2, ← h1]; exact e1.symm
      rw [e3, e2]
    exact Prod.ext hfst h1
  have step3 : ∑ q ∈ Pairs, wt r (q.1 ∪ q.2) * (p / r) ^ q.2.card
      = ∑ q ∈ Pairs.image φ, wt r q.1 * (p / r) ^ q.2.card := by
    rw [Finset.sum_image hinj]
  -- Step 4: the image is contained in the target set
  have step4 : Pairs.image φ ⊆ Target := by
    intro q hq
    simp only [Finset.mem_image, hPairs, Finset.mem_filter, Finset.mem_univ, true_and] at hq
    obtain ⟨q0, hq0, hEq⟩ := hq
    rw [hTarget, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · rw [← hEq]
      exact Ufam_subset_pick hq0
    · rw [← hEq]
      exact Ufam_card hq0
  have hnonneg : ∀ q : Finset α × Finset α, 0 ≤ wt r q.1 * (p / r) ^ q.2.card := by
    intro q
    have h1 : 0 ≤ wt r q.1 := wt_nonneg (le_of_lt hr0) hr1 _
    have h2 : 0 ≤ (p / r) ^ q.2.card := by positivity
    exact mul_nonneg h1 h2
  have step5 : ∑ q ∈ Pairs.image φ, wt r q.1 * (p / r) ^ q.2.card
      ≤ ∑ q ∈ Target, wt r q.1 * (p / r) ^ q.2.card :=
    Finset.sum_le_sum_of_subset_of_nonneg step4 (fun q _ _ => hnonneg q)
  -- Step 6: bound the sum over the target set
  have step6 : ∑ q ∈ Target, wt r q.1 * (p / r) ^ q.2.card ≤ (2 / c) ^ m := by
    have hsplit : ∑ q ∈ Target, wt r q.1 * (p / r) ^ q.2.card
        = ∑ Z : Finset α, ∑ U : Finset α,
            if U ⊆ pick H Z ∧ m ≤ 2 * U.card then wt r Z * (p / r) ^ U.card else 0 := by
      rw [hTarget, Finset.sum_filter, Fintype.sum_prod_type]
    rw [hsplit]
    have hinner : ∀ Z : Finset α,
        (∑ U : Finset α, if U ⊆ pick H Z ∧ m ≤ 2 * U.card then wt r Z * (p / r) ^ U.card else 0)
          ≤ wt r Z * (2 / c) ^ m := by
      intro Z
      have hwZ : 0 ≤ wt r Z := wt_nonneg (le_of_lt hr0) hr1 _
      have hstep : (∑ U : Finset α,
            if U ⊆ pick H Z ∧ m ≤ 2 * U.card then wt r Z * (p / r) ^ U.card else 0)
          = wt r Z * ∑ U : Finset α,
            if U ⊆ pick H Z ∧ m ≤ 2 * U.card then (p / r) ^ U.card else 0 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun U _ => ?_)
        by_cases h : U ⊆ pick H Z ∧ m ≤ 2 * U.card <;> simp [h]
      rw [hstep]
      refine mul_le_mul_of_nonneg_left ?_ hwZ
      -- bound the number of relevant `U` and each term
      have hterm : ∀ U : Finset α,
          (if U ⊆ pick H Z ∧ m ≤ 2 * U.card then (p / r) ^ U.card else 0)
            ≤ (if U ⊆ pick H Z then (1 / c) ^ m else 0) := by
        intro U
        by_cases h : U ⊆ pick H Z ∧ m ≤ 2 * U.card
        · rw [if_pos h, if_pos h.1, hpr]
          have : (1 / c ^ 2 : ℝ) ^ U.card = (1 / c) ^ (2 * U.card) := by
            rw [two_mul, pow_add, ← mul_pow]
            congr 1
            field_simp
          rw [this]
          exact pow_le_pow_of_le_one (by positivity) (by rw [div_le_one hc0]; linarith) h.2
        · rw [if_neg h]
          by_cases h2 : U ⊆ pick H Z
          · rw [if_pos h2]; positivity
          · rw [if_neg h2]
      calc (∑ U : Finset α,
            if U ⊆ pick H Z ∧ m ≤ 2 * U.card then (p / r) ^ U.card else 0)
          ≤ ∑ U : Finset α, if U ⊆ pick H Z then (1 / c) ^ m else 0 :=
            Finset.sum_le_sum (fun U _ => hterm U)
        _ = ((pick H Z).powerset.card : ℝ) * (1 / c) ^ m := by
            rw [← Finset.sum_filter]
            have : (Finset.univ.filter (fun U : Finset α => U ⊆ pick H Z))
                = (pick H Z).powerset := by
              ext U; simp
            rw [this, Finset.sum_const, nsmul_eq_mul]
        _ ≤ (2 ^ m : ℝ) * (1 / c) ^ m := by
            have hcard : ((pick H Z).powerset.card : ℝ) ≤ (2 ^ m : ℝ) := by
              rw [Finset.card_powerset]
              have := pick_card_le hH Z
              exact_mod_cast Nat.pow_le_pow_right (by norm_num) this
            have : (0:ℝ) ≤ (1 / c) ^ m := by positivity
            exact mul_le_mul_of_nonneg_right hcard this
        _ = (2 / c) ^ m := by
            rw [div_pow, div_pow]
            field_simp
            rw [one_pow]
    calc ∑ Z : Finset α, ∑ U : Finset α,
          (if U ⊆ pick H Z ∧ m ≤ 2 * U.card then wt r Z * (p / r) ^ U.card else 0)
        ≤ ∑ Z : Finset α, wt r Z * (2 / c) ^ m := Finset.sum_le_sum (fun Z _ => hinner Z)
      _ = (2 / c) ^ m := by rw [← Finset.sum_mul, sum_wt, one_mul]
  linarith [step1, step2, step3, step5, step6]

end KahnKalai

/-
Product ("Bernoulli") weights on the powerset of a finite set, and the two basic
identities we need:

* the total mass is `1`;
* the union of two independent random sets of densities `a` and `b` is a random
  set of density `a + b - a*b`.
-/
import Mathlib

open scoped BigOperators
open Finset

namespace KahnKalai

variable {α : Type*} [DecidableEq α]

/-- `wtOn s p A = p ^ |A| * (1-p) ^ (|s| - |A|)`: the probability that the `p`-random
subset of `s` equals `A` (for `A ⊆ s`). -/

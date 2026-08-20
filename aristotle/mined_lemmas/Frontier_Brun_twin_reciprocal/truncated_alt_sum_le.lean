import Mathlib
import RequestProject.Brun.Final

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

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The twin primes are indexed by the subtype of naturals `p` such that both `p` and `p + 2`
are prime, and the summand is `1 / p`. -/

lemma truncated_alt_sum_le (P : Finset ℕ) (a : ℕ → ℝ) (ha : ∀ p ∈ P, 0 ≤ a p) (k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p
      ≤ ∏ p ∈ P, (1 - a p) + (∏ p ∈ P, (1 + 2 * a p)) / 2 ^ (k + 1) := by
  classical
  set R := max (k + 1) (P.card + 1) with hR
  have hkR : k + 1 ≤ R := le_max_left _ _
  have hPR : P.card + 1 ≤ R := le_max_right _ _
  -- the full alternating sum is the product
  have hfull : ∑ j ∈ range R, (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p
      = ∏ p ∈ P, (1 - a p) := by
    have h1 : ∏ p ∈ P, (1 - a p) = ∑ S ∈ P.powerset, ∏ p ∈ S, (-(a p)) := by
      have := prod_one_add_eq_sum_powerset P (fun p => -(a p))
      simpa using this
    rw [h1, sum_powerset_eq_sum_range P (fun S => ∏ p ∈ S, (-(a p))) hPR]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun S hS => ?_)
    have hcard : S.card = j := (Finset.mem_powersetCard.mp hS).2
    rw [Finset.prod_neg, hcard]
  -- split off the tail
  have hsplit : ∑ j ∈ range R, (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p
      = (∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p)
        + ∑ j ∈ Ico (k + 1) R, (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p := by
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le (k + 1)) hkR]
  have hnn : ∀ j, ∀ S ∈ P.powersetCard j, 0 ≤ ∏ p ∈ S, a p := by
    intro j S hS
    refine Finset.prod_nonneg (fun p hp => ha p ?_)
    exact (Finset.mem_powersetCard.mp hS).1 hp
  -- bound the tail
  have htail : -(∑ j ∈ Ico (k + 1) R, (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p)
      ≤ (∏ p ∈ P, (1 + 2 * a p)) / 2 ^ (k + 1) := by
    have h1 : -(∑ j ∈ Ico (k + 1) R, (-1 : ℝ) ^ j * ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p)
        ≤ ∑ j ∈ Ico (k + 1) R, ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p := by
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_le_sum (fun j _ => ?_)
      have hs : 0 ≤ ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p :=
        Finset.sum_nonneg (hnn j)
      rcases Nat.even_or_odd j with hj | hj
      · rw [hj.neg_one_pow]
        linarith
      · rw [hj.neg_one_pow]
        linarith
    have h2 : ∑ j ∈ Ico (k + 1) R, ∑ S ∈ P.powersetCard j, ∏ p ∈ S, a p
        ≤ ∑ j ∈ Ico (k + 1) R, ∑ S ∈ P.powersetCard j, (∏ p ∈ S, (2 * a p)) / 2 ^ (k + 1) := by
      refine Finset.sum_le_sum (fun j hj => Finset.sum_le_sum (fun S hS => ?_))
      simp only [Finset.mem_Ico] at hj
      have hcard : S.card = j := (Finset.mem_powersetCard.mp hS).2
      have hprod : ∏ p ∈ S, (2 * a p) = 2 ^ S.card * ∏ p ∈ S, a p := by
        rw [Finset.prod_mul_distrib, Finset.prod_const]
      rw [hprod, hcard]
      have hnn' : 0 ≤ ∏ p ∈ S, a p := hnn j S hS
      rw [le_div_iff₀ (by positivity)]
      have : (2 : ℝ) ^ (k + 1) ≤ 2 ^ j := by
        apply pow_le_pow_right₀ (by norm_num) hj.1
      nlinarith
    have h3 : ∑ j ∈ Ico (k + 1) R, ∑ S ∈ P.powersetCard j, (∏ p ∈ S, (2 * a p)) / 2 ^ (k + 1)
        ≤ ∑ j ∈ range R, ∑ S ∈ P.powersetCard j, (∏ p ∈ S, (2 * a p)) / 2 ^ (k + 1) := by
      refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · intro j hj
        simp only [Finset.mem_Ico] at hj
        simp only [Finset.mem_range]
        omega
      · intro j _ _
        refine Finset.sum_nonneg (fun S hS => ?_)
        have : 0 ≤ ∏ p ∈ S, (2 * a p) := by
          refine Finset.prod_nonneg (fun p hp => ?_)
          have := ha p ((Finset.mem_powersetCard.mp hS).1 hp)
          linarith
        positivity
    have h4 : ∑ j ∈ range R, ∑ S ∈ P.powersetCard j, (∏ p ∈ S, (2 * a p)) / 2 ^ (k + 1)
        = (∏ p ∈ P, (1 + 2 * a p)) / 2 ^ (k + 1) := by
      rw [prod_one_add_eq_sum_powerset P (fun p => 2 * a p),
        sum_powerset_eq_sum_range P (fun S => ∏ p ∈ S, (2 * a p)) hPR, Finset.sum_div]
      refine Finset.sum_congr rfl (fun j _ => ?_)
      rw [Finset.sum_div]
    linarith
  linarith [hfull, hsplit, htail]

/-! ### The sieve bound -/


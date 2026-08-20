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

lemma card_primes_block_mul_le (j : ℕ) :
    (((range (2 ^ (j + 1) + 1)).filter (fun p => Nat.Prime p ∧ 2 ^ j < p)).card) * j
      ≤ 2 ^ (j + 2) := by
  set B := (range (2 ^ (j + 1) + 1)).filter (fun p => Nat.Prime p ∧ 2 ^ j < p) with hB
  have hsub : B ⊆ (range (2 ^ (j + 1) + 1)).filter (fun p => Nat.Prime p) := by
    intro p hp
    rw [hB, Finset.mem_filter] at hp
    exact Finset.mem_filter.mpr ⟨hp.1, hp.2.1⟩
  have h1 : ∏ p ∈ B, p ≤ primorial (2 ^ (j + 1)) := by
    rw [primorial]
    refine Finset.prod_le_prod_of_subset_of_one_le' hsub ?_
    intro p hp _
    exact (Finset.mem_filter.mp hp).2.one_lt.le
  have h2 : primorial (2 ^ (j + 1)) ≤ 4 ^ (2 ^ (j + 1)) := primorial_le_4_pow _
  have h3 : (2 ^ j) ^ B.card ≤ ∏ p ∈ B, p := by
    calc (2 ^ j) ^ B.card = ∏ _p ∈ B, 2 ^ j := by rw [Finset.prod_const]
      _ ≤ ∏ p ∈ B, p := Finset.prod_le_prod' (fun p hp =>
          le_of_lt (Finset.mem_filter.mp hp).2.2)
  have h4 : (2 : ℕ) ^ (j * B.card) ≤ 2 ^ (2 ^ (j + 2)) := by
    calc (2 : ℕ) ^ (j * B.card) = (2 ^ j) ^ B.card := by rw [pow_mul]
      _ ≤ ∏ p ∈ B, p := h3
      _ ≤ 4 ^ (2 ^ (j + 1)) := le_trans h1 h2
      _ = 2 ^ (2 ^ (j + 2)) := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          congr 1
          ring
  have h5 := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp h4
  rw [Nat.mul_comm]
  exact h5

/-- Block bound: the sum of `1/p` over primes in `(2^j, 2^(j+1)]` is at most `4/j`. -/

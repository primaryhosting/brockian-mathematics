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

/-
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring `/-! ... -/`,
-- so the header above is written as an ordinary block comment.)

import RequestProject.Brun.Summable

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.
Here the index type is the set of primes `p` such that `p + 2` is also prime. -/

lemma card_dyadic_block_mul_le (z j : ℕ) :
    (#((z + 1).primesBelow.filter (fun p => Nat.log 2 p = j))) * j ≤ 2 ^ (j + 2) := by
  set S := (z + 1).primesBelow.filter (fun p => Nat.log 2 p = j) with hS
  have hmem : ∀ p ∈ S, p.Prime ∧ 2 ^ j ≤ p ∧ p < 2 ^ (j + 1) := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    obtain ⟨hp1, hp2⟩ := hp
    have hpp := Nat.prime_of_mem_primesBelow hp1
    refine ⟨hpp, ?_, ?_⟩
    · have := Nat.pow_log_le_self 2 hpp.pos.ne'
      rwa [hp2] at this
    · have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p
      rwa [hp2] at this
  have hlow : (2 ^ j) ^ (#S) ≤ ∏ p ∈ S, p :=
    Finset.pow_card_le_prod S _ _ (fun p hp => (hmem p hp).2.1)
  have hsub : S ⊆ (Finset.range (2 ^ (j + 1) + 1)).filter Nat.Prime := by
    intro p hp
    have := hmem p hp
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), this.1⟩
  have hhigh : ∏ p ∈ S, p ≤ primorial (2 ^ (j + 1)) := by
    rw [primorial]
    exact Finset.prod_le_prod_of_subset_of_one_le' hsub
      (fun i hi _ => (Finset.mem_filter.mp hi).2.one_lt.le)
  have h4 : primorial (2 ^ (j + 1)) ≤ 4 ^ (2 ^ (j + 1)) := primorial_le_4_pow _
  have key : (2:ℕ) ^ (j * #S) ≤ 2 ^ (2 ^ (j + 2)) := by
    calc (2:ℕ) ^ (j * #S) = (2 ^ j) ^ (#S) := by rw [pow_mul]
      _ ≤ 4 ^ (2 ^ (j + 1)) := le_trans hlow (hhigh.trans h4)
      _ = 2 ^ (2 ^ (j + 2)) := by
          rw [show (4:ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
          ring_nf
  have h := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp key
  rw [Nat.mul_comm]
  exact h

/-- The reciprocals of the primes in a dyadic block `[2^j, 2^(j+1))` sum to at most `4/j`. -/

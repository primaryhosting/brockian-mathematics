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

lemma sum_indicator_block_le (n N : ℕ) :
    ∑ i ∈ (Finset.range n).filter (fun i => Nat.log 2 i = N),
      Set.indicator {p : ℕ | p.Prime ∧ (p + 2).Prime} (fun m => (1 : ℝ) / m) i
      ≤ (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N := by
  classical
  set S := (Finset.range n).filter (fun i => Nat.log 2 i = N) with hS
  have hstep : ∀ i ∈ S,
      Set.indicator {p : ℕ | p.Prime ∧ (p + 2).Prime} (fun m => (1 : ℝ) / m) i
        ≤ (if (i.Prime ∧ (i + 2).Prime) then ((1:ℝ) / 2 ^ N) else 0) := by
    intro i hi
    by_cases hti : i.Prime ∧ (i + 2).Prime
    · rw [Set.indicator_of_mem (show i ∈ {p : ℕ | p.Prime ∧ (p + 2).Prime} from hti),
        if_pos hti]
      have hipos : 0 < i := hti.1.pos
      have hlog : Nat.log 2 i = N := (Finset.mem_filter.mp hi).2
      have hile : (2:ℕ) ^ N ≤ i := by
        have := Nat.pow_log_le_self 2 hipos.ne'
        rwa [hlog] at this
      have hR : ((2:ℝ) ^ N) ≤ (i:ℝ) := by exact_mod_cast hile
      exact one_div_le_one_div_of_le (by positivity) hR
    · rw [Set.indicator_of_notMem (show i ∉ {p : ℕ | p.Prime ∧ (p + 2).Prime} from hti),
        if_neg hti]
  refine (Finset.sum_le_sum hstep).trans ?_
  rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul]
  have hcard : #(S.filter (fun i => i.Prime ∧ (i + 2).Prime)) ≤ twinCount (2 ^ (N + 1)) := by
    rw [twinCount]
    apply Finset.card_le_card
    intro i hi
    rw [Finset.mem_filter] at hi ⊢
    obtain ⟨hiS, hti⟩ := hi
    refine ⟨Finset.mem_range.mpr ?_, hti⟩
    have hlog : Nat.log 2 i = N := (Finset.mem_filter.mp hiS).2
    have hlt := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) i
    rw [hlog] at hlt
    omega
  have hcastc : ((#(S.filter (fun i => i.Prime ∧ (i + 2).Prime)) : ℝ))
      ≤ (twinCount (2 ^ (N + 1)) : ℝ) := by exact_mod_cast hcard
  calc (#(S.filter (fun i => i.Prime ∧ (i + 2).Prime)) : ℝ) * (1 / 2 ^ N)
      ≤ (twinCount (2 ^ (N + 1)) : ℝ) * (1 / 2 ^ N) :=
        mul_le_mul_of_nonneg_right hcastc (by positivity)
    _ = (twinCount (2 ^ (N + 1)) : ℝ) / 2 ^ N := by ring

/-- The indicator function of the twin primes, weighted by `1/p`, is summable. -/

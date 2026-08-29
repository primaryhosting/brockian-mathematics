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

import Mathlib

/-!
# Practical Twin Infinitude
Category: Brockian Conjecture
Target: Brockian.PracticalNumbers.PracticalTwinInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.PracticalNumbers

/-- A natural number `n` is *practical* if it is positive and every `t ≤ n` can be written
as a sum of distinct divisors of `n`. -/

theorem reach_two_mul_three_pow (j : ℕ) :
    ∃ D : Finset ℕ, D ⊆ (2 * 3 ^ j).divisors ∧ Reach D (T j) := by
  induction j with
  | zero =>
    refine ⟨{1, 2}, ?_, ?_⟩
    · intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> exact Nat.mem_divisors.mpr ⟨by norm_num, by norm_num⟩
    intro t ht
    simp only [T] at ht
    interval_cases t
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp⟩
    · exact ⟨{2}, by simp, by simp⟩
    · exact ⟨{1, 2}, by simp, by norm_num⟩
  | succ j ih =>
    obtain ⟨D, hD, hR⟩ := ih
    have h3 : (0:ℕ) < 3 ^ j := by positivity
    have hpow : (3:ℕ) ^ (j + 1) = 3 * 3 ^ j := by ring
    have hT := pow_le_T j
    have hstep1 : Reach (insert (3 ^ (j + 1)) D) (T j + 3 ^ (j + 1)) := by
      refine hR.step (by omega) ?_
      intro y hy
      have h1 : y ≤ 2 * 3 ^ j := le_of_mem_divisors (hD hy)
      omega
    have hstep2 : Reach (insert (2 * 3 ^ (j + 1)) (insert (3 ^ (j + 1)) D))
        (T j + 3 ^ (j + 1) + 2 * 3 ^ (j + 1)) := by
      refine hstep1.step (by omega) ?_
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · omega
      · have h1 : y ≤ 2 * 3 ^ j := le_of_mem_divisors (hD hy)
        omega
    refine ⟨insert (2 * 3 ^ (j + 1)) (insert (3 ^ (j + 1)) D), ?_, hstep2⟩
    intro x hx
    have hne : 2 * 3 ^ (j + 1) ≠ 0 := by positivity
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Nat.mem_divisors.mpr ⟨dvd_rfl, hne⟩
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact Nat.mem_divisors.mpr ⟨⟨2, by ring⟩, hne⟩
    · have hd := Nat.mem_divisors.mp (hD hx)
      exact Nat.mem_divisors.mpr ⟨hd.1.trans ⟨3, by rw [hpow]; ring⟩, hne⟩

/-- Every positive `x` has a power of three in the window `[x, 3x)`. -/

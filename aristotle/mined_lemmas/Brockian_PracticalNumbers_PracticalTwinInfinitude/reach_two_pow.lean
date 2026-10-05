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

theorem reach_two_pow (a : ℕ) :
    ∃ D : Finset ℕ, D ⊆ (2 ^ a).divisors ∧ Reach D (2 ^ (a + 1) - 1) := by
  induction a with
  | zero =>
    refine ⟨{1}, by simp, ?_⟩
    intro t ht
    norm_num at ht
    interval_cases t
    · exact ⟨∅, by simp, by simp⟩
    · exact ⟨{1}, by simp, by simp⟩
  | succ a ih =>
    obtain ⟨D, hD, hR⟩ := ih
    have hpos : (0:ℕ) < 2 ^ a := by positivity
    have hstep : Reach (insert (2 ^ (a + 1)) D) (2 ^ (a + 1) - 1 + 2 ^ (a + 1)) := by
      refine hR.step ?_ ?_
      · have : (1:ℕ) ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
        omega
      · intro y hy
        have h1 : y ≤ 2 ^ a := le_of_mem_divisors (hD hy)
        have h2 : (2:ℕ) ^ (a + 1) = 2 * 2 ^ a := by ring
        omega
    refine ⟨insert (2 ^ (a + 1)) D, ?_, ?_⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact Nat.mem_divisors.mpr ⟨dvd_rfl, by positivity⟩
      · have hd := Nat.mem_divisors.mp (hD hx)
        exact Nat.mem_divisors.mpr ⟨hd.1.trans (pow_dvd_pow 2 (Nat.le_succ a)), by positivity⟩
    · have heq : 2 ^ (a + 1) - 1 + 2 ^ (a + 1) = 2 ^ (a + 1 + 1) - 1 := by
        have h0 : (2:ℕ) ^ (a + 1 + 1) = 2 ^ (a + 1) + 2 ^ (a + 1) := by ring
        have h1 : (1:ℕ) ≤ 2 ^ (a + 1) := Nat.one_le_two_pow
        omega
      rwa [heq] at hstep

/-- The bound reached by the divisors `{3^i, 2·3^i : i ≤ j}` of `2 * 3^j`. -/

/-
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Furstenberg Szemeredi
Category: Frontier Abel
Target: Frontier.furstenberg_szemeredi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-- The counting function of a set of naturals: the number of elements of `A` below `n`. -/

theorem exists_pos_frequently_count (h : 0 < upperDensity A) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ 0 < n ∧ ε * n ≤ (count A n : ℝ) := by
  have hcobdd : Filter.IsCoboundedUnder (· ≤ ·) Filter.atTop
      (fun n : ℕ => (count A n : ℝ) / n) := by
    refine Filter.IsBoundedUnder.isCoboundedUnder_le ⟨0, ?_⟩
    rw [Filter.eventually_map]
    filter_upwards with n
    have : (0 : ℝ) ≤ (count A n : ℝ) / n := by positivity
    exact this
  have hlim : upperDensity A / 2 <
      Filter.limsup (fun n : ℕ => (count A n : ℝ) / n) Filter.atTop := by
    show upperDensity A / 2 < upperDensity A
    linarith
  have hfreq : ∃ᶠ n : ℕ in Filter.atTop, upperDensity A / 2 < (count A n : ℝ) / n :=
    Filter.frequently_lt_of_lt_limsup hcobdd hlim
  refine ⟨upperDensity A / 2, by linarith, fun N => ?_⟩
  obtain ⟨n, hn, hlt⟩ := (hfreq.and_eventually (Filter.eventually_ge_atTop N)).exists
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · simp at hn; linarith
    · exact hp
  refine ⟨n, hlt, hnpos, ?_⟩
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hnpos
  rw [lt_div_iff₀ hn0] at hn
  linarith

/-- Reduction: the finitary form of Szemerédi's theorem implies the density form. -/

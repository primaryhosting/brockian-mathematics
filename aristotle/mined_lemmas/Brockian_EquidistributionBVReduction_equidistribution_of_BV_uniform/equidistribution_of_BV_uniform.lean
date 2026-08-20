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
# Reduction of equidistribution to bounded-variation test functions

Let `x : ℕ → ℝ` be a sequence.  Assume that for **every** real function `f` of bounded
variation on `[0,1]` the Birkhoff-type averages

`(1/N) * ∑_{n < N} f (Int.fract (x n))`

converge to `∫₀¹ f`.  We show that the sequence `x` is then equidistributed modulo one, and
moreover *uniformly* so: the counting error over intervals `[a,b) ⊆ [0,1]` tends to `0`
uniformly in the endpoints (i.e. the discrepancy of the sequence tends to `0`).

The main statement is `equidistribution_of_BV_uniform`.  It is unconditional: apart from the
assumption on the sequence itself, no auxiliary result is taken as a hypothesis.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

open Filter Set MeasureTheory
open scoped Topology

namespace Brockian

open scoped Classical in
/-- The number of indices `n < N` for which the fractional part of `x n` lies in `[a, b)`. -/

theorem equidistribution_of_BV_uniform (x : ℕ → ℝ)
    (h : ∀ f : ℝ → ℝ, BoundedVariationOn f (Set.Icc (0:ℝ) 1) →
      Tendsto (fun N : ℕ => (∑ n ∈ Finset.range N, f (Int.fract (x n))) / N) atTop
        (𝓝 (∫ t in (0:ℝ)..1, f t)))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ 1 →
      |freq x N a b - (b - a)| < ε := by
  obtain ⟨N₀, hN₀, hmain⟩ := uniform_freq_zero x h (half_pos hε)
  refine ⟨N₀, fun N hN a b ha hab hb => ?_⟩
  have hNpos : (0:ℝ) < N := by
    have : 1 ≤ N := le_trans hN₀ hN
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one this
  have hsplit : freq x N a b = freq x N 0 b - freq x N 0 a := by
    unfold freq
    rw [cnt_split x N ha hab]
    push_cast
    ring
  have h1 := hmain N hN b (ha.trans hab) hb
  have h2 := hmain N hN a ha (hab.trans hb)
  rw [hsplit]
  have : freq x N 0 b - freq x N 0 a - (b - a)
      = (freq x N 0 b - b) - (freq x N 0 a - a) := by ring
  rw [this]
  calc |freq x N 0 b - b - (freq x N 0 a - a)|
      ≤ |freq x N 0 b - b| + |freq x N 0 a - a| := abs_sub _ _
    _ < ε / 2 + ε / 2 := add_lt_add h1 h2
    _ = ε := by ring

end Brockian


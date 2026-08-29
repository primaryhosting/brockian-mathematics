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
# Equidistribution Of Asymptotic
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Classical

open Filter Topology

namespace Brockian.Equidistribution

/-- The number of indices `n < N` whose fractional part `Int.fract (x n)` is `< c`. -/

lemma tendsto_edf_of_dense (x : ℕ → ℝ) (D : Set ℝ) (hD : Dense D)
    (hasym : ∀ c ∈ D, 0 ≤ c → c ≤ 1 → Tendsto (fun N => edf x N c) atTop (𝓝 c))
    {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    Tendsto (fun N => edf x N c) atTop (𝓝 c) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlow : ∀ᶠ N in atTop, c - ε < edf x N c := by
    rcases lt_or_ge (c - ε) 0 with h | h
    · filter_upwards with N using lt_of_lt_of_le h (edf_nonneg x N c)
    · obtain ⟨d, hdD, hd⟩ := hD.exists_between (show c - ε < c by linarith)
      have hd0 : (0:ℝ) ≤ d := le_of_lt (lt_of_le_of_lt h hd.1)
      have hd1 : d ≤ 1 := le_trans hd.2.le hc1
      have hev := (hasym d hdD hd0 hd1).eventually_const_lt hd.1
      filter_upwards [hev] with N hN
      exact lt_of_lt_of_le hN (edf_mono x N hd.2.le)
  have hhigh : ∀ᶠ N in atTop, edf x N c < c + ε := by
    rcases lt_or_ge 1 (c + ε) with h | h
    · filter_upwards with N using lt_of_le_of_lt (edf_le_one x N c) h
    · obtain ⟨d, hdD, hd⟩ := hD.exists_between (show c < c + ε by linarith)
      have hd0 : (0:ℝ) ≤ d := le_of_lt (lt_of_le_of_lt hc0 hd.1)
      have hd1 : d ≤ 1 := le_trans hd.2.le h
      have hev := (hasym d hdD hd0 hd1).eventually_lt_const hd.2
      filter_upwards [hev] with N hN
      exact lt_of_le_of_lt (edf_mono x N hd.1.le) hN
  obtain ⟨N₀, hN₀⟩ := (hlow.and hhigh).exists_forall_of_atTop
  refine ⟨N₀, fun N hN => ?_⟩
  obtain ⟨h1, h2⟩ := hN₀ N hN
  rw [Real.dist_eq, abs_sub_lt_iff]
  constructor <;> linarith

/-- **Equidistribution from asymptotics on a dense set of levels.**

Let `x : ℕ → ℝ` be a sequence.  Assume that for every level `c` in a dense set `D ⊆ ℝ`
with `0 ≤ c ≤ 1`, the proportion of the first `N` terms whose fractional part is `< c`
tends to `c`.  Then the sequence is equidistributed modulo one: for every subinterval
`[a, b) ⊆ [0, 1]`, the proportion of the first `N` terms whose fractional part lies in
`[a, b)` tends to `b - a`. -/

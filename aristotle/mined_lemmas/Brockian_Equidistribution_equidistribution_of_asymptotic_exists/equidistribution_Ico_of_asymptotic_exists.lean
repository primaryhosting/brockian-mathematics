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
# Equidistribution Of Asymptotic Exists
Category: Brockian (Open Discharge)
Target: Brockian.Equidistribution.equidistribution_of_asymptotic_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

open Filter Topology

set_option maxHeartbeats 1000000

namespace Brockian.Equidistribution

/-- `countBelow x N a` is the number of indices `n < N` whose fractional part
`Int.fract (x n)` is smaller than `a`. -/

theorem equidistribution_Ico_of_asymptotic_exists
    (x : ℕ → ℝ) (D : Set ℝ)
    (hD : ∀ u v : ℝ, 0 ≤ u → u < v → v ≤ 1 → ∃ d ∈ D, u < d ∧ d < v)
    (hlim : ∀ a ∈ D, Tendsto (fun N => prop x N a) atTop (𝓝 a))
    {a b : ℝ} (ha0 : 0 ≤ a) (hab : a ≤ b) (hb1 : b ≤ 1) :
    Tendsto (fun N => (countIn x N a b : ℝ) / N) atTop (𝓝 (b - a)) := by
  have key : ∀ N : ℕ, (countIn x N a b : ℝ) / N = prop x N b - prop x N a := by
    intro N
    have h := congrArg (fun m : ℕ => (m : ℝ)) (countBelow_add_countIn x N hab)
    push_cast at h
    rw [prop, prop, div_sub_div_same]
    congr 1
    linarith
  simp only [key]
  exact (equidistribution_of_asymptotic_exists x D hD hlim (ha0.trans hab) hb1).sub
    (equidistribution_of_asymptotic_exists x D hD hlim ha0 (hab.trans hb1))

end Brockian.Equidistribution


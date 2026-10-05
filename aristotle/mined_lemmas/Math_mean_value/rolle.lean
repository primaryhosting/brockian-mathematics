/-
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A self-contained development of the mean value theorem: the interior extremum
principle gives Rolle's theorem, and Rolle's theorem applied to an auxiliary
function gives the mean value theorem.
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

namespace Math

open Set

/-- If `f` attains a maximum over `[a, b]` at an interior point `x`, its derivative
there vanishes. -/

theorem rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hcont : ContinuousOn f (Icc a b))
    (hfab : f a = f b) : ∃ c ∈ Ioo a b, deriv f c = 0 := by
  have hne : (Icc a b).Nonempty := nonempty_Icc.2 hab.le
  obtain ⟨x, hxmem, hxmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  obtain ⟨y, hymem, hymin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  -- If either extremum is attained at an interior point we are done.
  by_cases hxi : x ∈ Ioo a b
  · exact ⟨x, hxi, deriv_eq_zero_of_isMaxOn_Icc hxi hxmax⟩
  by_cases hyi : y ∈ Ioo a b
  · exact ⟨y, hyi, deriv_eq_zero_of_isMinOn_Icc hyi hymin⟩
  -- Otherwise both extrema are at endpoints, so `f` is constant on `[a, b]`.
  have hxa : f x = f a := by
    rcases eq_or_lt_of_le hxmem.1 with h | h
    · rw [← h]
    · rcases eq_or_lt_of_le hxmem.2 with h' | h'
      · rw [h', hfab]
      · exact absurd ⟨h, h'⟩ hxi
  have hya : f y = f a := by
    rcases eq_or_lt_of_le hymem.1 with h | h
    · rw [← h]
    · rcases eq_or_lt_of_le hymem.2 with h' | h'
      · rw [h', hfab]
      · exact absurd ⟨h, h'⟩ hyi
  have hconst : ∀ z ∈ Icc a b, f z = f a := by
    intro z hz
    have h1 : f z ≤ f x := hxmax hz
    have h2 : f y ≤ f z := hymin hz
    rw [hxa] at h1
    rw [hya] at h2
    linarith
  have hc : (a + b) / 2 ∈ Ioo a b := ⟨by linarith, by linarith⟩
  exact ⟨(a + b) / 2, hc, deriv_eq_zero_of_constantOn_Icc hc hconst⟩

/-- The derivative of the auxiliary function `f x - s * x` at an interior point where `f`
is differentiable. -/

/-
# Ivt
Category: Pure Mathematics
Target: Math.ivt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Set

namespace Math

/-- **Intermediate value theorem.** A real-valued function that is continuous on the
closed interval `[a, b]` (with `a ≤ b`) attains every value `y` lying between `f a` and
`f b`. -/
theorem ivt {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Icc a b))
    {y : ℝ} (hy₁ : min (f a) (f b) ≤ y) (hy₂ : y ≤ max (f a) (f b)) :
    ∃ c ∈ Icc a b, f c = y := by
  have huIcc : uIcc a b = Icc a b := uIcc_of_le hab
  have hmem : y ∈ uIcc (f a) (f b) := by
    rw [uIcc_eq_union]
    rcases le_total (f a) (f b) with h | h
    · left
      constructor
      · simpa [min_eq_left h] using hy₁
      · simpa [max_eq_right h] using hy₂
    · right
      constructor
      · simpa [min_eq_right h] using hy₁
      · simpa [max_eq_left h] using hy₂
  have hsub : uIcc (f a) (f b) ⊆ f '' uIcc a b :=
    intermediate_value_uIcc (by rwa [huIcc])
  obtain ⟨c, hc, hcy⟩ := hsub hmem
  exact ⟨c, huIcc ▸ hc, hcy⟩

end Math

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


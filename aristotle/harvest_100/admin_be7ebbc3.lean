/-
# Ivt
Category: Pure Mathematics
Target: Math.ivt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ivt
Category: Pure Mathematics
Target: Math.ivt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Intermediate value theorem.** If `f : ℝ → ℝ` is continuous on `[a, b]` (with `a ≤ b`)
and `y` lies between `f a` and `f b`, then `f` attains the value `y` at some point of `[a, b]`.

The key Mathlib ingredient is `intermediate_value_uIcc`:
`ContinuousOn f (Set.uIcc a b) → Set.uIcc (f a) (f b) ⊆ f '' Set.uIcc a b`. -/
theorem ivt {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    {y : ℝ} (hy : y ∈ Set.uIcc (f a) (f b)) :
    ∃ c ∈ Set.Icc a b, f c = y := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hf' : ContinuousOn f (Set.uIcc a b) := by rwa [huIcc]
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc hf' hy
  exact ⟨c, huIcc ▸ hc, hfc⟩

/-- Ordered form of the intermediate value theorem: if `f a ≤ y ≤ f b`, then `y` is attained
on `[a, b]`. -/
theorem ivt_of_le {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    {y : ℝ} (hy₁ : f a ≤ y) (hy₂ : y ≤ f b) :
    ∃ c ∈ Set.Icc a b, f c = y :=
  ivt hab hf (Set.mem_uIcc_of_le hy₁ hy₂)

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


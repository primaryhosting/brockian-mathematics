import Mathlib

/-!
# Ivt
Category: Pure Mathematics
Target: Math.ivt
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

namespace Math

/-- **Intermediate value theorem.** If `f` is continuous on `[a, b]` (with `a ≤ b`) and `y`
lies between `f a` and `f b` (i.e. `y ∈ [f a, f b]` in either order, written `Set.uIcc`),
then `f` attains the value `y` at some point of `[a, b]`. -/
theorem ivt {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    {y : ℝ} (hy : y ∈ Set.uIcc (f a) (f b)) : ∃ c ∈ Set.Icc a b, f c = y := by
  have h : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc (f := f) (a := a) (b := b) (by rw [h]; exact hf) hy
  exact ⟨c, by rwa [h] at hc, hfc⟩

/-- Explicit `min`/`max` form of the intermediate value theorem. -/
theorem ivt_of_min_le_le_max {f : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (h₁ : min (f a) (f b) ≤ y) (h₂ : y ≤ max (f a) (f b)) :
    ∃ c ∈ Set.Icc a b, f c = y :=
  ivt hab hf (Set.mem_Icc.mpr ⟨h₁, h₂⟩)

end Math


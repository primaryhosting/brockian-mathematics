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

/-- **Intermediate value theorem.** A real-valued function that is continuous on the
closed interval `[a, b]` (with `a ≤ b`) attains every value `y` lying between `f a`
and `f b`; the value `y` is allowed to be on either side, since it is only assumed to
lie in the unordered interval `Set.uIcc (f a) (f b)`. -/
theorem ivt {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) {y : ℝ} (hy : y ∈ Set.uIcc (f a) (f b)) :
    ∃ c ∈ Set.Icc a b, f c = y := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have h : y ∈ f '' Set.uIcc a b :=
    intermediate_value_uIcc (by rwa [huIcc]) hy
  rw [huIcc] at h
  obtain ⟨c, hc, hcy⟩ := h
  exact ⟨c, hc, hcy⟩

end Math


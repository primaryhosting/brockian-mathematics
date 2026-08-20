/-
# Ivt
Category: Pure Mathematics
Target: Math.ivt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Math

/-- **Intermediate value theorem.** A function `f` continuous on the closed interval `[a, b]`
(with `a ≤ b`) attains every value `y` lying between `f a` and `f b`: there is a point
`c ∈ [a, b]` with `f c = y`.

The proof reduces to Mathlib's `intermediate_value_uIcc`, which states
`Set.uIcc (f a) (f b) ⊆ f '' Set.uIcc a b` for `f` continuous on `Set.uIcc a b`. -/
theorem ivt {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    {y : ℝ} (hy : min (f a) (f b) ≤ y ∧ y ≤ max (f a) (f b)) :
    ∃ c ∈ Set.Icc a b, f c = y := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have hf' : ContinuousOn f (Set.uIcc a b) := by rwa [huIcc]
  have hmem : y ∈ Set.uIcc (f a) (f b) := by
    rw [Set.uIcc, Set.mem_Icc]
    exact ⟨by simpa using hy.1, by simpa using hy.2⟩
  obtain ⟨c, hc, hfc⟩ := intermediate_value_uIcc hf' hmem
  exact ⟨c, huIcc ▸ hc, hfc⟩

end Math


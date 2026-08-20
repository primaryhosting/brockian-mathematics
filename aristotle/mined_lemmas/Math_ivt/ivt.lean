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

/-!
# Ivt
Category: Pure Mathematics
Target: Math.ivt
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math

/-- **Intermediate value theorem.** If `f` is continuous on `[a, b]` (with `a ≤ b`) and `y`
lies between `f a` and `f b` (in either order, expressed via the unordered interval
`Set.uIcc (f a) (f b)`), then `f` attains the value `y` at some point of `[a, b]`.

The proof is Mathlib's `intermediate_value_uIcc`. -/

theorem ivt {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    {y : ℝ} (hy : y ∈ Set.uIcc (f a) (f b)) :
    ∃ c ∈ Set.Icc a b, f c = y := by
  have huIcc : Set.uIcc a b = Set.Icc a b := Set.uIcc_of_le hab
  have h := intermediate_value_uIcc (a := a) (b := b) (f := f) (by rwa [huIcc])
  obtain ⟨c, hc, hfc⟩ := h hy
  exact ⟨c, huIcc ▸ hc, hfc⟩

end Math


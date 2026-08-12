/-
# Extreme Value
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.extreme_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Extreme Value
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.extreme_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Analysis

/-- **Extreme value theorem**: a real-valued function that is continuous on a nonempty
compact set `s` attains its maximum on `s`. -/
theorem extreme_value {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ}
    (hs : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x := by
  obtain ⟨x, hxs, hx⟩ := IsCompact.exists_isMaxOn hs hne hf
  exact ⟨x, hxs, fun y hy => hx hy⟩

/-- The same statement phrased via `IsMaxOn`: the maximum is attained at some point of `s`. -/
theorem extreme_value_isMaxOn {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ}
    (hs : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ x ∈ s, IsMaxOn f s x :=
  IsCompact.exists_isMaxOn hs hne hf

end Analysis


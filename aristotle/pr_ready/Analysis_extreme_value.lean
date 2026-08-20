/-!
# Extreme Value
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.extreme_value
Statement: The extreme value theorem: a continuous real-valued function on a nonempty compact set attains its maximum. State: for a nonempty compact set s and f continuous on s, there exists x in s with forall y in s, f y <= f x. (Use Mathlib's IsCompact.exists_forall_ge / exists_isMaxOn.)
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-
# Extreme Value
Category: Frontier Wave 2 (deeper machinery)
Target: Analysis.extreme_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


namespace Analysis

/-- **Extreme value theorem**: a real-valued function that is continuous on a nonempty
compact set `s` attains a maximum value on `s`: there is a point `x ∈ s` with `f y ≤ f x`
for all `y ∈ s`. -/
theorem extreme_value {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ}
    (hs : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
  let ⟨x, hx, hmax⟩ := IsCompact.exists_isMaxOn hs hne hf
  ⟨x, hx, fun _ hy => hmax hy⟩

/-- Variant phrased with `IsMaxOn`. -/
theorem extreme_value_isMaxOn {X : Type*} [TopologicalSpace X] {s : Set X} {f : X → ℝ}
    (hs : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ x ∈ s, IsMaxOn f s x :=
  IsCompact.exists_isMaxOn hs hne hf

end Analysis


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

open scoped Classical

set_option autoImplicit false

namespace Analysis

variable {X : Type*} [TopologicalSpace X]

/-- Key intermediate lemma: the continuous image of a nonempty compact set is a nonempty
compact set of reals, hence it is bounded above and contains its supremum. -/

theorem exists_mem_image_forall_le {s : Set X} {f : X → ℝ}
    (hs : IsCompact s) (hne : s.Nonempty) (hf : ContinuousOn f s) :
    ∃ M ∈ f '' s, ∀ z ∈ f '' s, z ≤ M := by
  have himg : IsCompact (f '' s) := hs.image_of_continuousOn hf
  have hinj : (f '' s).Nonempty := hne.image f
  obtain ⟨M, hM, hMmax⟩ := himg.exists_isGreatest hinj
  exact ⟨M, hM, fun z hz => hMmax hz⟩

/-- **Extreme value theorem**: a real-valued function that is continuous on a nonempty
compact set attains its maximum on that set. -/

/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of sets is a *sunflower with core `c`* if any two distinct members of `S`
intersect exactly in `c`. -/

lemma colorClass_disjoint {X : Finset α} {m : ℕ} {f : ∀ a ∈ X, Fin m} {i j : Fin m} (hij : i ≠ j) :
    Disjoint (colorClass X f i) (colorClass X f j) := by
  rw [Finset.disjoint_left]
  intro a hai haj
  obtain ⟨h1, h2⟩ := mem_colorClass.mp hai
  obtain ⟨h3, h4⟩ := mem_colorClass.mp haj
  exact hij (h2 ▸ h4 ▸ rfl)

/-- The set of all colourings of `X` with `m` colours. -/

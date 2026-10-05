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

lemma mem_colorClass {X : Finset α} {m : ℕ} {f : ∀ a ∈ X, Fin m} {i : Fin m} {a : α} :
    a ∈ colorClass X f i ↔ ∃ h : a ∈ X, f a h = i := by
  constructor
  · intro ha
    rw [colorClass, Finset.mem_image] at ha
    obtain ⟨b, hb, hba⟩ := ha
    rw [Finset.mem_filter] at hb
    obtain ⟨bv, hbX⟩ := b
    subst hba
    exact ⟨hbX, hb.2⟩
  · rintro ⟨h, hf⟩
    rw [colorClass, Finset.mem_image]
    exact ⟨⟨a, h⟩, Finset.mem_filter.mpr ⟨Finset.mem_attach _ _, hf⟩, rfl⟩


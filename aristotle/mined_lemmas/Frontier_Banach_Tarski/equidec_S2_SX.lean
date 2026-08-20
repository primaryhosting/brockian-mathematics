import RequestProject.BT.Ball

/-!
# Banach Tarski
Category: Frontier — Set Theory
Target: Frontier.Banach_Tarski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Metric Set
open scoped Pointwise

namespace Frontier

/-- The vector by which the second copy of the ball is translated. -/

theorem equidec_S2_SX : Equidec (E ≃ₗᵢ[ℝ] E) S2 SX := by
  obtain ⟨g, hg⟩ := exists_absorbing_rotation poles poles_countable poles_subset
  have hsub : ∀ n : ℕ, (g ^ n) • poles ⊆ S2 := by
    rintro n x ⟨y, hy, rfl⟩
    exact linIso_mem_S2 _ (poles_subset hy)
  exact Equidec.absorb g poles S2 hsub hg

/-- **The Hausdorff paradox**: the unit sphere in `ℝ³` is paradoxical. -/

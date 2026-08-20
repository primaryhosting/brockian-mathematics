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

theorem trans (h₁ : Equidec G A B) (h₂ : Equidec G B C) : Equidec G A C := by
  classical
  obtain ⟨f, S, hbij, hdec⟩ := h₁
  obtain ⟨f', S', hbij', hdec'⟩ := h₂
  exact ⟨f' ∘ f, S' * S, hbij'.comp hbij, hdec'.comp hdec hbij.mapsTo⟩


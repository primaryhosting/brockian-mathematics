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

theorem symm [Nonempty X] (h : Equidec G A B) : Equidec G B A := by
  classical
  obtain ⟨f, S, hbij, hdec⟩ := h
  refine ⟨invFunOn f A, S⁻¹, hbij.symm hbij.invOn_invFunOn.symm, ?_⟩
  have := hdec.of_leftInvOn hbij.injOn.leftInvOn_invFunOn
  rwa [hbij.image_eq] at this


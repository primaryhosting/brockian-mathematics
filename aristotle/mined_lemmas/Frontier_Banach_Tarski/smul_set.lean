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

theorem smul_set (g : G) (A : Set X) : Equidec G A (g • A) := by
  refine ⟨fun x => g • x, {g}, ⟨fun x hx => ⟨x, hx, rfl⟩, fun x _ y _ h => by
    simpa using congrArg (fun z => g⁻¹ • z) h, fun x hx => ?_⟩, fun a _ => ⟨g, by simp⟩⟩
  obtain ⟨y, hy, rfl⟩ := hx
  exact ⟨y, hy, rfl⟩

/-- Transport an equidecomposition along a group homomorphism compatible with the actions. -/

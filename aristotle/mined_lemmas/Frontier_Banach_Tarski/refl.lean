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

theorem refl (A : Set X) : Equidec G A A :=
  ⟨id, {1}, Set.bijOn_id A, fun a _ => ⟨1, by simp⟩⟩


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

theorem doubling (hP : Paradoxical G A) (hAB : Equidec G A B) (hdisj : Disjoint A B) :
    Equidec G A (A ∪ B) := by
  obtain ⟨A₁, A₂, hunion, hd, h₁, h₂⟩ := hP
  have h := Equidec.union hd hdisj h₁ (h₂.trans hAB)
  rwa [hunion] at h

/-- Transport paradoxicality along a group homomorphism compatible with the actions. -/

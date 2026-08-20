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

noncomputable def gCenter : E ≃ᵢ E :=
  IsometryEquiv.addRight pHalf * toIso (rotZ (Real.cos 1) (Real.sin 1) cos_one_sin_one) *
    (IsometryEquiv.addRight pHalf)⁻¹


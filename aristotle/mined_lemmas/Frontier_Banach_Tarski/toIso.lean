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

def toIso : (E ≃ₗᵢ[ℝ] E) →* (E ≃ᵢ E) where
  toFun f := f.toIsometryEquiv
  map_one' := rfl
  map_mul' _ _ := rfl


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

def orbitSetoid : Setoid ↥SX where
  r x y := ∃ w : FreeGroup (Fin 2), phi w (x : E) = (y : E)
  iseqv := by
    refine ⟨fun x => ⟨1, by simp⟩, ?_, ?_⟩
    · rintro x y ⟨w, hw⟩
      refine ⟨w⁻¹, ?_⟩
      rw [map_inv, ← hw]
      exact (phi w).symm_apply_apply _
    · rintro x y z ⟨w, hw⟩ ⟨v, hv⟩
      exact ⟨v * w, by rw [map_mul]; simp only [LinearIsometryEquiv.coe_mul,
        Function.comp_apply, hw, hv]⟩

/-- A set of representatives for the orbits of the free group action on `SX`. -/

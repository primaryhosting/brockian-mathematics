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

theorem phi_mapsTo (w : FreeGroup (Fin 2)) {x : E} (hx : x ∈ SX) : phi w x ∈ SX := by
  refine ⟨linIso_mem_S2 _ hx.1, ?_⟩
  rintro ⟨-, v, hv, hvx⟩
  refine hx.2 ⟨hx.1, w⁻¹ * v * w, ?_, ?_⟩
  · intro h
    apply hv
    have : v = w * w⁻¹ * v * w * w⁻¹ := by group
    rw [this]
    rw [show w * w⁻¹ * v * w * w⁻¹ = w * (w⁻¹ * v * w) * w⁻¹ by group, h]
    group
  · have : phi (w⁻¹ * v * w) x = (phi w)⁻¹ (phi v (phi w x)) := by
      rw [map_mul, map_mul, map_inv]
      rfl
    rw [this, hvx]
    exact (phi w).symm_apply_apply x

/-- The action of the free group on `SX` is free. -/

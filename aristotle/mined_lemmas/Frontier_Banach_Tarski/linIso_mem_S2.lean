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

theorem linIso_mem_S2 (g : E ≃ₗᵢ[ℝ] E) {x : E} (hx : x ∈ S2) : g x ∈ S2 := by
  rw [mem_S2] at hx ⊢
  rw [g.norm_map, hx]

/-- The set of poles: points of the sphere fixed by some nontrivial element of the free
group of rotations. -/

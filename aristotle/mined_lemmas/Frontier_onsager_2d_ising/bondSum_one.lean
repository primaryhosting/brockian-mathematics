import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Frontier

/-! ## The finite-volume 2D Ising model on an `L × L` torus -/

/-- Shift a periodic (torus) index by one site. -/

theorem bondSum_one (σ : Config 1) : bondSum σ = 2 := by
  rw [bondSum, Fintype.sum_prod_type]
  simp [spin, shiftIdx]
  cases h : σ (0, 0) <;> norm_num

/-- The `1 × 1` torus: each of the two configurations has two (self-)bonds, so
`Z₁(K) = 2 e^{2K}`. -/

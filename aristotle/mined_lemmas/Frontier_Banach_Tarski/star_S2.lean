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

theorem star_S2 : star S2 = closedBall (0 : E) 1 \ {0} := by
  ext y
  simp only [star, Set.mem_setOf_eq, Set.mem_diff, Metric.mem_closedBall, dist_zero_right,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨hy0, hy1, -⟩
    exact ⟨hy1, hy0⟩
  · rintro ⟨hy1, hy0⟩
    refine ⟨hy0, hy1, ?_⟩
    rw [mem_S2, norm_smul]
    simp only [norm_inv, Real.norm_eq_abs, abs_norm]
    field_simp


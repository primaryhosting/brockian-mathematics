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

theorem norm_eq_of_sq {x y : E} (h : x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 = y 0 ^ 2 + y 1 ^ 2 + y 2 ^ 2) :
    ‖x‖ = ‖y‖ := by
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simp only [Fin.sum_univ_three, sq_abs, Real.norm_eq_abs]
  simpa using h

/-- The linear map given by the rotation matrix about the `z`-axis with cosine `c`, sine `s`. -/

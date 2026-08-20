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

def rotX (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) : E ≃ₗᵢ[ℝ] E where
  toLinearEquiv := LinearEquiv.ofLinear (rotXlin c s) (rotXlin c (-s))
    (by
      ext x i
      fin_cases i <;> simp
      · linear_combination (x 1) * h
      · linear_combination (x 2) * h)
    (by
      ext x i
      fin_cases i <;> simp
      · linear_combination (x 1) * h
      · linear_combination (x 2) * h)
  norm_map' x := by
    show ‖rotXlin c s x‖ = ‖x‖
    rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
    congr 1
    simp [Fin.sum_univ_three, sq_abs, rotXlin]
    nlinarith [h]


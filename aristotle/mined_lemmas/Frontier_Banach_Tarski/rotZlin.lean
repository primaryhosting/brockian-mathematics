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

def rotZlin (c s : ℝ) : E →ₗ[ℝ] E where
  toFun x := !₂[c * x 0 - s * x 1, s * x 0 + c * x 1, x 2]
  map_add' x y := by ext i; fin_cases i <;> simp <;> ring
  map_smul' a x := by ext i; fin_cases i <;> simp <;> ring

/-- The linear map given by the rotation matrix about the `x`-axis with cosine `c`, sine `s`. -/

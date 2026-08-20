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

theorem rotX_mul (c s c' s' : ℝ) (h : c ^ 2 + s ^ 2 = 1) (h' : c' ^ 2 + s' ^ 2 = 1)
    (h'' : (c * c' - s * s') ^ 2 + (s * c' + c * s') ^ 2 = 1) :
    rotX c s h * rotX c' s' h' = rotX (c * c' - s * s') (s * c' + c * s') h'' := by
  apply LinearIsometryEquiv.ext
  intro x
  ext i
  fin_cases i <;> simp <;> ring


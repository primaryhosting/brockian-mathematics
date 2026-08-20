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

theorem rotX_symm (c s : ℝ) (h : c ^ 2 + s ^ 2 = 1) (h' : c ^ 2 + (-s) ^ 2 = 1) :
    (rotX c s h)⁻¹ = rotX c (-s) h' := by
  have key : rotX c (-s) h' * rotX c s h = 1 := by
    have e1 : c * c - -s * s = 1 := by nlinarith [h]
    have e2 : -s * c + c * s = 0 := by ring
    have h'' : (c * c - -s * s) ^ 2 + (-s * c + c * s) ^ 2 = 1 := by rw [e1, e2]; norm_num
    rw [rotX_mul c (-s) c s h' h h'']
    simp only [e1, e2]
    exact rotX_one _
  exact inv_eq_of_mul_eq_one_left key

/-- The powers of a rotation about the `z`-axis. -/

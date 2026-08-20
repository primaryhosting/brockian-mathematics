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

theorem rotZ_pow (t : ℝ) (n : ℕ) (h : Real.cos t ^ 2 + Real.sin t ^ 2 = 1)
    (hn : Real.cos (n * t) ^ 2 + Real.sin (n * t) ^ 2 = 1) :
    (rotZ (Real.cos t) (Real.sin t) h) ^ n = rotZ (Real.cos (n * t)) (Real.sin (n * t)) hn := by
  induction n with
  | zero =>
    apply LinearIsometryEquiv.ext
    intro x
    ext i
    fin_cases i <;> simp
  | succ n ih =>
    have hn' : Real.cos (n * t) ^ 2 + Real.sin (n * t) ^ 2 = 1 := Real.cos_sq_add_sin_sq _
    rw [pow_succ, ih hn']
    apply LinearIsometryEquiv.ext
    intro x
    have key : ((n : ℝ) + 1) * t = (n : ℝ) * t + t := by ring
    ext i
    fin_cases i <;> simp [key, Real.cos_add, Real.sin_add] <;> ring

end BT

/-
Two rotations of `ℝ³` by the angle `arccos (1/3)` about the `z`- and `x`-axes generate a
free group of rank two.
-/
import RequestProject.BT.Rotations

namespace BT

open Real


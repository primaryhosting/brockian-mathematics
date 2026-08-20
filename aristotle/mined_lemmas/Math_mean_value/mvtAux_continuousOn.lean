/-
# Mean Value
Category: Pure Mathematics
Target: Math.mean_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open Set

namespace Math

/-- The auxiliary function used in the proof of the Mean Value Theorem: `f` corrected by the
linear function with slope `(f b - f a) / (b - a)`. -/

theorem mvtAux_continuousOn {f : ℝ → ℝ} {a b : ℝ} (hfc : ContinuousOn f (Icc a b)) :
    ContinuousOn (mvtAux f a b) (Icc a b) :=
  hfc.sub ((continuous_const.mul continuous_id).continuousOn)

/-- At each interior point where `f` is differentiable, the auxiliary function has derivative
`deriv f x - (f b - f a) / (b - a)`. -/

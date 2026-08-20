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

noncomputable def mvtAux (f : ℝ → ℝ) (a b : ℝ) : ℝ → ℝ :=
  fun x => f x - ((f b - f a) / (b - a)) * x

/-- The auxiliary function takes the same value at the two endpoints. -/

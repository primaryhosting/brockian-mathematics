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

theorem mvtAux_endpoints {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) :
    mvtAux f a b a = mvtAux f a b b := by
  have hba : b - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt hab)
  simp only [mvtAux]
  field_simp
  ring

/-- The auxiliary function is continuous on `[a, b]` whenever `f` is. -/

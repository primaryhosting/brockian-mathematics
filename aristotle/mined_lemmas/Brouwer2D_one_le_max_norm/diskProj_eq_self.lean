/-
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brouwer 2 D
Category: Pure Mathematics
Target: Math.brouwer_2d
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Metric Set

namespace Brouwer2D

/-! ### The radial retraction of the plane onto the closed unit disk -/

/-- The radial retraction of `ℂ` onto the closed unit disk. -/

lemma diskProj_eq_self {z : ℂ} (hz : ‖z‖ ≤ 1) : diskProj z = z := by
  have : max 1 ‖z‖ = 1 := max_eq_left hz
  simp [diskProj, this]

/-! ### Continuous logarithms on the plane -/

/-- Any nonvanishing continuous function on `ℂ` has a continuous logarithm,
by the lifting property of the covering map `exp : ℂ → ℂ \ {0}`. -/

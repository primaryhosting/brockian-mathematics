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

lemma continuous_diskProj : Continuous diskProj := by
  refine Continuous.smul ?_ continuous_id
  exact (continuous_const.max continuous_norm).inv₀ fun z =>
    ne_of_gt (lt_of_lt_of_le one_pos (one_le_max_norm z))


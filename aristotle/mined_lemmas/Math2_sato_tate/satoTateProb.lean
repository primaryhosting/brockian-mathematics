/-
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sato Tate
Category: Frontier Math
Target: Math2.sato_tate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real ENNReal NNReal Classical
open MeasureTheory Filter Topology Set

namespace Math2

/-- The Sato–Tate density on `[0, π]`: `θ ↦ (2/π) sin²θ`. -/

noncomputable def satoTateProb : ProbabilityMeasure ℝ := ⟨satoTateMeasure, inferInstance⟩

/-- The Sato–Tate measure has no atoms. -/

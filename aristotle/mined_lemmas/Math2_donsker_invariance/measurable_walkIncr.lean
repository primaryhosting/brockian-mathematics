/-
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Donsker Invariance
Category: Frontier Math
Target: Math2.donsker_invariance
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace Math2

/-- The linearly interpolated, rescaled random walk
`W_n(t) = (S_{⌊nt⌋} + (nt - ⌊nt⌋) X_{⌊nt⌋}) / √n`, where `S_m = X_0 + ⋯ + X_{m-1}`.
This is the classical Donsker polygonal process associated to the steps `X`. -/

lemma measurable_walkIncr {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (u : ℕ → ℝ) (n j : ℕ) :
    Measurable (walkIncr X u n j) :=
  (Finset.measurable_sum _ fun i _ ↦ hmeas i).div_const _

/-- The increments of the rescaled walk are centred Gaussian. -/

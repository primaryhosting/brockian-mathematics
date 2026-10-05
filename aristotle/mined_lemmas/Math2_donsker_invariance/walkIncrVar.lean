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

noncomputable def walkIncrVar (u : ℕ → ℝ) (n j : ℕ) : ℝ≥0 :=
  (((⌊(n : ℝ) * u (j + 1)⌋₊ - ⌊(n : ℝ) * u j⌋₊ : ℕ) : ℝ) / n).toNNReal

/-- The linear map sending a vector of increments to the vector of its partial sums. -/

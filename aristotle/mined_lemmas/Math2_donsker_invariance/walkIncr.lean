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

noncomputable def walkIncr {Ω : Type*} (X : ℕ → Ω → ℝ) (u : ℕ → ℝ) (n j : ℕ) (ω : Ω) : ℝ :=
  (∑ i ∈ Finset.Ico ⌊(n : ℝ) * u j⌋₊ ⌊(n : ℝ) * u (j + 1)⌋₊, X i ω) / Real.sqrt n

/-- The variance of `walkIncr X u n j` for standard Gaussian steps. -/

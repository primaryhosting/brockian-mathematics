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

noncomputable def donskerInterp {Ω : Type*} (X : ℕ → Ω → ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  ((∑ i ∈ Finset.range ⌊(n : ℝ) * t⌋₊, X i ω)
      + ((n : ℝ) * t - ⌊(n : ℝ) * t⌋₊) * X ⌊(n : ℝ) * t⌋₊ ω) / Real.sqrt n

/-- The variance of `donskerInterp X n t` when the steps are standard Gaussian:
`(⌊nt⌋ + (nt - ⌊nt⌋)²)/n`. -/

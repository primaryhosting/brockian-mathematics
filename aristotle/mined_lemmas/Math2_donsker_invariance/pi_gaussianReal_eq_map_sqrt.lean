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

lemma pi_gaussianReal_eq_map_sqrt {k : ℕ} (v : Fin k → ℝ≥0) :
    (Measure.pi fun j : Fin k ↦ gaussianReal 0 (v j))
      = (Measure.pi fun _ : Fin k ↦ gaussianReal 0 1).map fun x j ↦ Real.sqrt (v j) * x j := by
  rw [Measure.pi_map_pi fun j ↦ (by fun_prop :
    AEMeasurable (fun x : ℝ ↦ Real.sqrt (v j) * x) (gaussianReal 0 1))]
  congr 1
  funext j
  exact gaussianReal_eq_map_sqrt (v j)

/-- Weak convergence of products of centred Gaussian laws when the variances converge. -/

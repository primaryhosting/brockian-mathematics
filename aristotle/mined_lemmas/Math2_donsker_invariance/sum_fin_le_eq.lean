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

lemma sum_fin_le_eq {k : ℕ} (g : ℕ → ℝ) (j : Fin k) :
    ∑ i : Fin k, (if (i : ℕ) ≤ (j : ℕ) then g i else 0)
      = ∑ i ∈ Finset.range ((j : ℕ) + 1), g i := by
  classical
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ if i ≤ (j : ℕ) then g i else 0) k, ← Finset.sum_filter]
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- A product of centred Gaussian measures is the image of the standard Gaussian product measure
under the diagonal scaling by the square roots of the variances. -/

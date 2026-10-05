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

lemma measurable_donskerInterp {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (n : ℕ) (t : ℝ) :
    Measurable (donskerInterp X n t) :=
  ((Finset.measurable_sum _ fun i _ ↦ hmeas i).add ((hmeas _).const_mul _)).div_const _

/-- The law of the rescaled walk at time `t` converges weakly to the centred Gaussian law with
variance `t`. -/

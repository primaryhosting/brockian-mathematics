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

lemma map_walkIncr_vector {X : ℕ → Ω → ℝ} (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (hlaw : ∀ i, P.map (X i) = gaussianReal 0 1) {u : ℕ → ℝ} (hu : Monotone u) (n k : ℕ) :
    P.map (fun ω (j : Fin k) ↦ walkIncr X u n (j : ℕ) ω)
      = Measure.pi fun j : Fin k ↦ gaussianReal 0 (walkIncrVar u n (j : ℕ)) := by
  rw [(iIndepFun_iff_map_fun_eq_pi_map fun j ↦
    (measurable_walkIncr hmeas u n (j : ℕ)).aemeasurable).1
      (iIndepFun_walkIncr hmeas hindep hlaw hu n k)]
  congr 1
  funext j
  exact map_walkIncr hmeas hindep hlaw u n (j : ℕ)

/-- The variances of the increments converge to the lengths of the time intervals. -/

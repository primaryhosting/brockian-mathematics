/- (Note: Lean requires `import` to be the first command, so this required header is
rendered as a plain block comment rather than a module doc-comment.)

# Eigenvalue Cauchy Schwarz Count

Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators

namespace Zeta23Redux.LinAlg

/-- The eigenvalues at most `theta` contribute nonpositively to `∑ (ev i - theta)`. -/

lemma sum_sub_le_sum_filter_sub {d : ℕ} (ev : Fin d → ℝ) (theta : ℝ) :
    ∑ i : Fin d, (ev i - theta)
      ≤ ∑ i ∈ Finset.univ.filter (fun i => theta < ev i), (ev i - theta) := by
  classical
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hs
  have hsplit : ∑ i : Fin d, (ev i - theta)
      = (∑ i ∈ s, (ev i - theta)) + ∑ i ∈ sᶜ, (ev i - theta) := by
    rw [← Finset.sum_add_sum_compl s (fun i => ev i - theta)]
  have hneg : ∑ i ∈ sᶜ, (ev i - theta) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have : ¬ (theta < ev i) := by
      simpa [hs, Finset.mem_compl, Finset.mem_filter] using hi
    linarith [not_lt.mp this]
  rw [hsplit]
  linarith

/-- Thresholded Cauchy–Schwarz count at the eigenvalue level (Lemma 3.3):
if `theta ≥ 0` and the total `∑ ev` exceeds `theta * d`, then the excess squared is bounded
by the number `n` of eigenvalues above `theta` times the sum of squares of all eigenvalues. -/

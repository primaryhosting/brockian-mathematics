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
theorem eigenvalue_cauchy_schwarz_count
    (d : ℕ) (ev : Fin d → ℝ) (theta : ℝ) (htheta : 0 ≤ theta)
    (s : Finset (Fin d)) (hs : s = Finset.univ.filter (fun i => theta < ev i))
    (n : ℕ) (hn : n = s.card)
    (hgt : theta * (d : ℝ) < ∑ i : Fin d, ev i) :
    (∑ i : Fin d, ev i - theta * (d : ℝ)) ^ 2 ≤ (n : ℝ) * ∑ i : Fin d, (ev i) ^ 2 := by
  classical
  subst hs
  subst hn
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hsdef
  -- Step 1: the excess is `∑ (ev i - theta)`
  have hexcess : ∑ i : Fin d, ev i - theta * (d : ℝ) = ∑ i : Fin d, (ev i - theta) := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  -- Step 2: bound by the sum over `s`
  have h1 : ∑ i : Fin d, (ev i - theta) ≤ ∑ i ∈ s, (ev i - theta) :=
    sum_sub_le_sum_filter_sub ev theta
  -- Step 3: drop the `-theta` on `s`
  have h2 : ∑ i ∈ s, (ev i - theta) ≤ ∑ i ∈ s, ev i := by
    apply Finset.sum_le_sum
    intro i _
    linarith
  have hpos : 0 < ∑ i : Fin d, ev i - theta * (d : ℝ) := by linarith
  have hle : ∑ i : Fin d, ev i - theta * (d : ℝ) ≤ ∑ i ∈ s, ev i := by
    rw [hexcess]; exact le_trans h1 h2
  -- Step 4: square and apply Cauchy–Schwarz on `s`
  have hsq : (∑ i : Fin d, ev i - theta * (d : ℝ)) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := by
    apply pow_le_pow_left₀ (le_of_lt hpos) hle
  have hcs : (∑ i ∈ s, ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hsub : ∑ i ∈ s, (ev i) ^ 2 ≤ ∑ i : Fin d, (ev i) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    intro i _ _
    positivity
  have hcard : (0 : ℝ) ≤ (s.card : ℝ) := by positivity
  nlinarith [hsq, hcs, mul_le_mul_of_nonneg_left hsub hcard]

end Zeta23Redux.LinAlg


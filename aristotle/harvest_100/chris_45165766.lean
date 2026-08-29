/-
# Eigenvalue Cauchy Schwarz Count
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.eigenvalue_cauchy_schwarz_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 1000000

namespace Zeta23Redux.LinAlg

/-- **Thresholded Cauchy–Schwarz count (Lemma 3.3, eigenvalue level).**
If `theta ≥ 0` and the total mass `∑ ev i` exceeds `theta * d`, then the excess squared is
bounded by the number `n` of eigenvalues above `theta` times the sum of squares of all
eigenvalues. -/
theorem eigenvalue_cauchy_schwarz_count
    (d : ℕ) (ev : Fin d → ℝ) (theta : ℝ) (htheta : 0 ≤ theta)
    (s : Finset (Fin d)) (hs : s = Finset.univ.filter (fun i => theta < ev i))
    (n : ℕ) (hn : n = s.card)
    (hsum : theta * (d : ℝ) < ∑ i, ev i) :
    (∑ i, ev i - theta * (d : ℝ)) ^ 2 ≤ (n : ℝ) * ∑ i, (ev i) ^ 2 := by
  subst hs hn
  set s : Finset (Fin d) := Finset.univ.filter (fun i => theta < ev i) with hsdef
  -- The excess is a sum of `ev i - theta`
  have hexcess : ∑ i, ev i - theta * (d : ℝ) = ∑ i, (ev i - theta) := by
    rw [Finset.sum_sub_distrib]
    simp [mul_comm]
  -- Split the sum over `s` and its complement
  have hsplit : ∑ i, (ev i - theta) = (∑ i ∈ s, (ev i - theta)) + ∑ i ∈ sᶜ, (ev i - theta) := by
    rw [Finset.sum_add_sum_compl]
  have hcompl : ∑ i ∈ sᶜ, (ev i - theta) ≤ 0 := by
    apply Finset.sum_nonpos
    intro i hi
    have : ¬ (theta < ev i) := by
      simpa [hsdef, Finset.mem_compl, Finset.mem_filter] using hi
    linarith [not_lt.mp this]
  have hle1 : ∑ i, (ev i - theta) ≤ ∑ i ∈ s, ev i := by
    have h2 : ∑ i ∈ s, (ev i - theta) ≤ ∑ i ∈ s, ev i := by
      rw [Finset.sum_sub_distrib]
      have : (0:ℝ) ≤ (s.card : ℝ) * theta := by positivity
      simp only [Finset.sum_const, nsmul_eq_mul]
      linarith
    rw [hsplit]; linarith
  have hA : 0 < ∑ i ∈ s, ev i := by
    have hpos : 0 < ∑ i, (ev i - theta) := by rw [← hexcess]; linarith
    linarith
  have hstep : (∑ i, ev i - theta * (d : ℝ)) ^ 2 ≤ (∑ i ∈ s, ev i) ^ 2 := by
    have h1 : 0 < ∑ i, ev i - theta * (d : ℝ) := by linarith
    have h2 : ∑ i, ev i - theta * (d : ℝ) ≤ ∑ i ∈ s, ev i := by
      rw [hexcess]; exact hle1
    nlinarith
  have hCS : (∑ i ∈ s, ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  have hmono : ∑ i ∈ s, (ev i) ^ 2 ≤ ∑ i, (ev i) ^ 2 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    intro i _ _
    positivity
  have hfin : (s.card : ℝ) * ∑ i ∈ s, (ev i) ^ 2 ≤ (s.card : ℝ) * ∑ i, (ev i) ^ 2 := by
    have : (0:ℝ) ≤ (s.card : ℝ) := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left hmono this
  linarith

end Zeta23Redux.LinAlg


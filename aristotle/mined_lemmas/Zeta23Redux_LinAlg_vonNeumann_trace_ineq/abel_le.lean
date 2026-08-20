/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators
open Finset

namespace Zeta23Redux.LinAlg

/-- Abel summation / Hardy–Littlewood–Pólya: if `m` is decreasing on `range d` and the partial
sums of `f` are dominated by those of `g`, with equal total sums, then `∑ m f ≤ ∑ m g`. -/

lemma abel_le (d : ℕ) (m f g : ℕ → ℝ)
    (hm : ∀ i j, i ≤ j → j < d → m j ≤ m i)
    (hpart : ∀ k, k ≤ d → ∑ i ∈ range k, f i ≤ ∑ i ∈ range k, g i)
    (htot : ∑ i ∈ range d, f i = ∑ i ∈ range d, g i) :
    ∑ i ∈ range d, m i * f i ≤ ∑ i ∈ range d, m i * g i := by
  set h : ℕ → ℝ := fun i => f i - g i with hh
  have key : ∑ i ∈ range d, m i * h i ≤ 0 := by
    have hbp := Finset.sum_range_by_parts m h d
    simp only [smul_eq_mul] at hbp
    have h0 : ∑ i ∈ range d, h i = 0 := by
      simp [hh, Finset.sum_sub_distrib, htot]
    rw [hbp, h0, mul_zero, zero_sub, neg_nonpos]
    apply Finset.sum_nonneg
    intro i hi
    rw [Finset.mem_range] at hi
    have hle : m (i + 1) ≤ m i := hm i (i + 1) (by omega) (by omega)
    have hs : ∑ j ∈ range (i + 1), h j ≤ 0 := by
      have := hpart (i + 1) (by omega)
      simp only [hh, Finset.sum_sub_distrib]
      linarith
    nlinarith
  have hsplit : ∑ i ∈ range d, m i * h i
      = ∑ i ∈ range d, m i * f i - ∑ i ∈ range d, m i * g i := by
    simp [hh, mul_sub, Finset.sum_sub_distrib]
  linarith [key, hsplit]

/-- If `0 ≤ c j ≤ 1` with `∑_{j<d} c j = k` and `n` is decreasing, then
`∑_{j<d} c j * n j ≤ ∑_{j<k} n j`. -/

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

lemma dstoch_le (d : ℕ) (S : ℕ → ℕ → ℝ) (m n : ℕ → ℝ)
    (hS0 : ∀ i j, i < d → j < d → 0 ≤ S i j)
    (hrow : ∀ i, i < d → ∑ j ∈ range d, S i j = 1)
    (hcol : ∀ j, j < d → ∑ i ∈ range d, S i j = 1)
    (hm : ∀ i j, i ≤ j → j < d → m j ≤ m i)
    (hn : ∀ i j, i ≤ j → j < d → n j ≤ n i) :
    ∑ i ∈ range d, ∑ j ∈ range d, m i * n j * S i j ≤ ∑ i ∈ range d, m i * n i := by
  set t : ℕ → ℝ := fun i => ∑ j ∈ range d, S i j * n j with ht
  have hrewrite : ∑ i ∈ range d, ∑ j ∈ range d, m i * n j * S i j
      = ∑ i ∈ range d, m i * t i := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [ht]
    simp only [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [hrewrite]
  apply abel_le d m t n hm
  · intro k hkd
    have hcomm : ∑ i ∈ range k, t i = ∑ j ∈ range d, (∑ i ∈ range k, S i j) * n j := by
      rw [ht, Finset.sum_comm]
      exact Finset.sum_congr rfl (fun j _ => by rw [Finset.sum_mul])
    rw [hcomm]
    apply partial_le d k hkd _ n
    · intro j hj
      exact Finset.sum_nonneg
        (fun i hi => hS0 i j (by have := Finset.mem_range.mp hi; omega) hj)
    · intro j hj
      calc ∑ i ∈ range k, S i j ≤ ∑ i ∈ range d, S i j := by
            apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hkd)
            intro i hi _
            exact hS0 i j (Finset.mem_range.mp hi) hj
        _ = 1 := hcol j hj
    · rw [Finset.sum_comm]
      have hone : ∀ i ∈ range k, ∑ j ∈ range d, S i j = 1 := fun i hi =>
        hrow i (by have := Finset.mem_range.mp hi; omega)
      rw [Finset.sum_congr rfl hone]
      simp
    · exact hn
  · rw [ht, Finset.sum_comm]
    have hone : ∀ j ∈ range d, ∑ i ∈ range d, S i j * n j = n j := by
      intro j hj
      rw [← Finset.sum_mul, hcol j (Finset.mem_range.mp hj), one_mul]
    rw [Finset.sum_congr rfl hone]

/-- The doubly stochastic bilinear bound, indexed by `Fin d`. -/

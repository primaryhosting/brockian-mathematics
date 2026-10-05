import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₀`, with vertices indexed by `ZMod 10`:
`i` and `j` are adjacent iff they differ by `1` modulo `10`. -/

lemma dft_inj (V : ZMod 10 → ℂ) (h : ∀ k : ZMod 10, (∑ j : ZMod 10, V j * ee (j * k)) = 0) :
    V = 0 := by
  funext j0
  have key : (0 : ℂ) = ∑ j : ZMod 10, V j * (if j - j0 = 0 then (10 : ℂ) else 0) := by
    calc (0 : ℂ) = ∑ k : ZMod 10, (∑ j : ZMod 10, V j * ee (j * k)) * ee (-(j0 * k)) := by
          simp [h]
      _ = ∑ k : ZMod 10, ∑ j : ZMod 10, V j * ee ((j - j0) * k) := by
          refine Finset.sum_congr rfl ?_
          intro k _
          rw [Finset.sum_mul]
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [mul_assoc, ← ee_add]
          congr 2
          ring
      _ = ∑ j : ZMod 10, ∑ k : ZMod 10, V j * ee ((j - j0) * k) := Finset.sum_comm
      _ = ∑ j : ZMod 10, V j * (if j - j0 = 0 then (10 : ℂ) else 0) := by
          refine Finset.sum_congr rfl ?_
          intro j _
          rw [← Finset.mul_sum, sum_ee]
  simp only [sub_eq_zero, mul_ite, mul_zero, Finset.sum_ite_eq' Finset.univ j0] at key
  simp at key
  simpa using key

/-- The Fourier coefficients of an eigenvector diagonalize the cyclic recurrence. -/

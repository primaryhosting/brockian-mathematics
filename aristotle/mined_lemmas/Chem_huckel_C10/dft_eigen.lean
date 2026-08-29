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

lemma dft_eigen (V : ZMod 10 → ℂ) (c : ℂ)
    (hrec : ∀ i : ZMod 10, V (i - 1) + V (i + 1) = c * V i) (k : ZMod 10) :
    (ee k + ee (-k)) * (∑ j : ZMod 10, V j * ee (j * k))
      = c * (∑ j : ZMod 10, V j * ee (j * k)) := by
  have hS1 : ∑ j : ZMod 10, V (j - 1) * ee (j * k) = ee k * ∑ j : ZMod 10, V j * ee (j * k) := by
    rw [← Equiv.sum_comp (Equiv.addRight (1 : ZMod 10)) (fun j : ZMod 10 => V (j - 1) * ee (j * k))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [Equiv.coe_addRight, add_sub_cancel_right]
    rw [show (j + 1) * k = j * k + k by ring, ee_add]
    ring
  have hS2 : ∑ j : ZMod 10, V (j + 1) * ee (j * k)
      = ee (-k) * ∑ j : ZMod 10, V j * ee (j * k) := by
    rw [← Equiv.sum_comp (Equiv.addRight (-1 : ZMod 10))
      (fun j : ZMod 10 => V (j + 1) * ee (j * k))]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro j _
    simp only [Equiv.coe_addRight]
    rw [show j + -1 + 1 = j by ring, show (j + -1) * k = j * k + -k by ring, ee_add]
    ring
  calc (ee k + ee (-k)) * (∑ j : ZMod 10, V j * ee (j * k))
      = (∑ j : ZMod 10, V (j - 1) * ee (j * k)) + ∑ j : ZMod 10, V (j + 1) * ee (j * k) := by
        rw [hS1, hS2, add_mul]
    _ = ∑ j : ZMod 10, (V (j - 1) + V (j + 1)) * ee (j * k) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = c * (∑ j : ZMod 10, V j * ee (j * k)) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [hrec j]; ring

/-- **Hückel theory for the C₁₀ cycle.**  A real number `μ` is an eigenvalue of the adjacency
matrix of the cycle graph `C₁₀` if and only if `μ = 2 cos (2πk/10)` for some `k ∈ {0, …, 9}`. -/

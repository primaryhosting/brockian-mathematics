import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/

lemma fourier_inversion (v : Fin 7 → ℂ) (j : Fin 7) :
    ∑ k : Fin 7, ee (j * k) * (∑ i : Fin 7, ee (-(i * k)) * v i) = 7 * v j := by
  have step : ∀ k : Fin 7, ee (j * k) * (∑ i : Fin 7, ee (-(i * k)) * v i)
      = ∑ i : Fin 7, ee (k * (j - i)) * v i := by
    intro k
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h : k * (j - i) = j * k + -(i * k) := by decide +revert
    rw [h, ee_add]
    ring
  simp only [step]
  rw [Finset.sum_comm]
  have hrow : ∀ i : Fin 7, ∑ k : Fin 7, ee (k * (j - i)) * v i
      = (if j - i = 0 then (7 : ℂ) else 0) * v i := by
    intro i
    rw [← Finset.sum_mul, sum_ee]
  simp only [hrow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hij
    have h : j - i ≠ 0 := sub_ne_zero_of_ne (Ne.symm hij)
    simp [h]
  · intro h
    exact absurd (Finset.mem_univ j) h


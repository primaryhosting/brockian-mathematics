import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Chem

open Complex Polynomial Matrix

/-- The primitive 18-th root of unity `exp (2πi/18)`. -/

lemma ee_sum (d : ℤ) :
    (∑ k : Fin 18, ee ((k : ℕ) * d)) = if (18 : ℤ) ∣ d then 18 else 0 := by
  split_ifs with h
  · have h1 : ∀ k : Fin 18, ee ((k : ℕ) * d) = 1 := by
      intro k
      rw [ee_congr (b := 0) (by simpa using Dvd.dvd.mul_left h _), ee]
      simp
    simp [h1]
  · have hx : ee d ≠ 1 := ee_ne_one h
    have h18 : (ee d) ^ (18 : ℕ) = 1 := by
      rw [← ee_pow]
      exact (ee_congr (b := 0) (by simp)).trans (by simp [ee])
    have hsum : (∑ k : Fin 18, ee ((k : ℕ) * d)) = ∑ i ∈ Finset.range 18, (ee d) ^ i := by
      rw [Fin.sum_univ_eq_sum_range (fun i => ee ((i : ℕ) * d))]
      exact Finset.sum_congr rfl fun i _ => ee_pow i d
    rw [hsum, geom_sum_eq hx, h18]
    simp

/-- The (unnormalized) discrete Fourier matrix of size 18. -/

/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the C₁₄ ring

The adjacency eigenvalues of the cycle graph `C₁₄` are exactly the numbers
`2 * cos (2πk/14)` for `k = 0, …, 13`.
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

lemma fourier_inversion (v : Fin 14 → ℂ) (x : Fin 14) :
    ∑ k : Fin 14, ch (k * x) * fcoeff v k = 14 * v x := by
  have h1 : ∀ k : Fin 14, ch (k * x) * fcoeff v k
      = ∑ y : Fin 14, ch (k * (x - y)) * v y := by
    intro k
    rw [fcoeff, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun y _ => ?_)
    rw [← mul_assoc, ← ch_add, fin_mul_sub_eq]
  simp only [h1]
  rw [Finset.sum_comm]
  have h2 : ∀ y : Fin 14, ∑ k : Fin 14, ch (k * (x - y)) * v y
      = (if x - y = 0 then (14 : ℂ) else 0) * v y := by
    intro y
    rw [← Finset.sum_mul, sum_ch]
  simp only [h2]
  have h3 : ∀ y : Fin 14, (if x - y = 0 then (14 : ℂ) else 0) * v y
      = if y = x then (14 : ℂ) * v y else 0 := by
    intro y
    by_cases h : y = x
    · subst h; simp
    · rw [if_neg h, if_neg (fun hc => h (by rw [sub_eq_zero] at hc; exact hc.symm)), zero_mul]
  simp only [h3]
  rw [Finset.sum_ite_eq' Finset.univ x (fun y => (14 : ℂ) * v y)]
  simp

/-- The eigenvalue attached to the character index `k`. -/

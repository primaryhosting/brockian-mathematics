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

lemma sum_ch (d : Fin 14) : ∑ k : Fin 14, ch (k * d) = if d = 0 then 14 else 0 := by
  by_cases hd : d = 0
  · subst hd
    simp [ch_zero]
  · simp only [hd, if_false]
    set S := ∑ k : Fin 14, ch (k * d) with hS
    have key : ch d * S = S := by
      calc ch d * S = ∑ k : Fin 14, ch ((k + 1) * d) := by
            rw [hS, Finset.mul_sum]
            refine Finset.sum_congr rfl (fun k _ => ?_)
            rw [add_mul, one_mul, ch_add, mul_comm]
        _ = S := Fintype.sum_equiv (Equiv.addRight (1 : Fin 14)) _ _ (fun k => rfl)
    have hz : (ch d - 1) * S = 0 := by rw [sub_mul, one_mul, key, sub_self]
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd ((ch_eq_one_iff d).1 (by linear_combination h)) hd
    · exact h

/-- The discrete Fourier coefficients of a function on `Fin 14`. -/

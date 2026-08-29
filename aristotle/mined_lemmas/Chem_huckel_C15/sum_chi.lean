import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The primitive 15-th root of unity `exp(2πi/15)`. -/

lemma sum_chi (a : ZMod 15) :
    ∑ k : ZMod 15, chi (k * a) = if a = 0 then 15 else 0 := by
  by_cases ha : a = 0
  · subst ha; simp [chi_zero]
  · simp only [ha, if_false]
    set S := ∑ k : ZMod 15, chi (k * a) with hS
    have hshift : ∑ k : ZMod 15, chi ((k + 1) * a) = S := by
      rw [hS]
      exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod 15)) _ _ (fun k => rfl)
    have hexp : ∑ k : ZMod 15, chi ((k + 1) * a) = chi a * S := by
      rw [hS, Finset.mul_sum]
      refine Finset.sum_congr rfl (fun k _ => ?_)
      rw [add_mul, one_mul, chi_add, mul_comm]
    have : chi a * S = S := by rw [← hexp, hshift]
    have hne : chi a - 1 ≠ 0 := sub_ne_zero_of_ne ((chi_eq_one_iff a).not.mpr ha)
    have : (chi a - 1) * S = 0 := by linear_combination this
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hne
    · exact h

/-- The two neighbours of `i` in `C₁₅`. -/

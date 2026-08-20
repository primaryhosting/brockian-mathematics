import Mathlib
/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Complex Matrix

namespace Chem

/-- A primitive 13-th root of unity. -/

lemma e13_sum (m : ZMod 13) : ∑ k : ZMod 13, e13 (k * m) = if m = 0 then 13 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp
  · simp only [hm, if_false]
    have h1 : e13 m * ∑ k : ZMod 13, e13 (k * m) = ∑ k : ZMod 13, e13 (k * m) := by
      rw [Finset.mul_sum]
      have hstep : ∀ k : ZMod 13, e13 m * e13 (k * m) = e13 ((k + 1) * m) := by
        intro k
        rw [add_mul, one_mul, e13_add, mul_comm]
      simp_rw [hstep]
      exact Fintype.sum_equiv (Equiv.addRight (1 : ZMod 13)) _ _ (fun k => rfl)
    have h2 : (e13 m - 1) * ∑ k : ZMod 13, e13 (k * m) = 0 := by
      rw [sub_mul, one_mul, h1, sub_self]
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd (sub_eq_zero.mp h) (e13_ne_one hm)
    · exact h

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`. -/

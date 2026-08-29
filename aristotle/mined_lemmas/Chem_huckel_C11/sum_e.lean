/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Hückel theory for the cycle C₁₁

The adjacency eigenvalues of the cycle graph `C₁₁` are exactly `2 cos (2πk/11)`, `k = 0,…,10`.
-/

open Complex Matrix Finset

namespace Chem

instance : Fact (Nat.Prime 11) := ⟨by norm_num⟩

/-! ## The cycle graph and its adjacency matrix -/

/-- The cycle graph on 11 vertices, realised on `ZMod 11`: `i ~ j` iff `i - j = ±1`. -/

lemma sum_e : ∑ n : ZMod 11, e n = 0 := by
  have key : om * ∑ n : ZMod 11, e n = ∑ n : ZMod 11, e n := by
    rw [Finset.mul_sum]
    exact Fintype.sum_equiv (Equiv.addLeft (1 : ZMod 11)) _ _
      (fun x => by simp [e_add, e_one])
  have h2 : (om - 1) * ∑ n : ZMod 11, e n = 0 := by linear_combination key
  rcases mul_eq_zero.1 h2 with h | h
  · exact absurd (sub_eq_zero.1 h) om_ne_one
  · exact h


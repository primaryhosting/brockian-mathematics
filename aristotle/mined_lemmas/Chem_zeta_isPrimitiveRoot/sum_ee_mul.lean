import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/

lemma sum_ee_mul (d : ZMod 13) : ∑ k : ZMod 13, ee (k * d) = if d = 0 then 13 else 0 := by
  haveI : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  by_cases hd : d = 0
  · subst hd
    simp [ee_zero, Finset.card_univ]
  · rw [if_neg hd]
    rw [← sum_ee]
    exact Fintype.sum_equiv (Equiv.mulRight₀ d hd) _ _ (fun k => rfl)

/-- The (unnormalised) discrete Fourier transform matrix. -/

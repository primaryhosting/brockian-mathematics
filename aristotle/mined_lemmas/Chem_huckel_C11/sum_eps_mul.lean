/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- A primitive 11-th root of unity. -/

lemma sum_eps_mul (d : ZMod 11) :
    ∑ k : ZMod 11, eps (k * d) = if d = 0 then (11 : ℂ) else 0 := by
  haveI : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  by_cases hd : d = 0
  · subst hd
    simp [eps_zero]
  · rw [if_neg hd]
    have h : ∑ k : ZMod 11, eps (k * d) = ∑ k : ZMod 11, eps k :=
      Fintype.sum_equiv (Equiv.mulRight₀ d hd) _ _ (fun _ => rfl)
    rw [h, sum_eps_univ]

/-- The Fourier eigenvectors of the cycle. -/

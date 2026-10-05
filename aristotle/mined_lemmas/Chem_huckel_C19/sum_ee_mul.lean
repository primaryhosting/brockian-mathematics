/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the cycle `C₁₉`

We show that the spectrum of the adjacency matrix of the cycle graph `C₁₉`
(the Hückel matrix of the annulene `C₁₉` in units where `α = 0`, `β = 1`)
is exactly `{2 cos (2πk/19) : k = 0, …, 18}`.

The proof diagonalizes the circulant adjacency matrix by the discrete Fourier matrix.
-/

namespace Chem

open Complex Matrix Finset

instance : Fact (Nat.Prime 19) := ⟨by norm_num⟩

/-- A primitive 19-th root of unity. -/

lemma sum_ee_mul (c : ZMod 19) : ∑ k : ZMod 19, ee (k * c) = if c = 0 then 19 else 0 := by
  by_cases hc : c = 0
  · simp [hc, ee_zero, Finset.card_univ]
  · simp only [hc, if_false]
    have h2 : ∑ k : ZMod 19, ee (k * c) = ∑ k : ZMod 19, ee k :=
      Fintype.sum_equiv (Equiv.mulRight₀ c hc) _ _ (fun x => by simp [Equiv.mulRight₀])
    rw [h2, sum_ee]


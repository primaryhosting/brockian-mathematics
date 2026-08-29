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

lemma C19adj_apply (i k : ZMod 19) :
    C19adj i k = (if k = i + 1 then (1 : ℂ) else 0) + (if k = i - 1 then 1 else 0) := by
  have key : (i - k = 1 ∨ k - i = 1) ↔ (k = i + 1 ∨ k = i - 1) := by
    constructor
    · rintro (h | h)
      · right; rw [← h]; ring
      · left; rw [← h]; ring
    · rintro (h | h) <;> subst h <;> [right; left] <;> ring
  have hne : (i + 1 : ZMod 19) ≠ i - 1 := by
    intro h
    have h2 : (2 : ZMod 19) = 0 := by linear_combination h
    revert h2; decide
  simp only [C19adj, key]
  by_cases h1 : k = i + 1
  · subst h1; simp [hne]
  · by_cases h2 : k = i - 1 <;> simp [h1, h2, Ne.symm hne]


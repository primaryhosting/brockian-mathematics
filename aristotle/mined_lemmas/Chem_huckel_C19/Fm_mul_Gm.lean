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

lemma Fm_mul_Gm : Fm * Gm = 1 := by
  ext i j
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 19, Fm i k * Gm k j = (19 : ℂ)⁻¹ * ee (k * (i - j)) := by
    intro k
    simp only [Fm, Gm]
    rw [show k * (i - j) = i * k - k * j by ring, ee_sub]
    ring
  rw [Finset.sum_congr rfl (fun k _ => h k), ← Finset.mul_sum, sum_ee_mul]
  rcases eq_or_ne i j with hij | hij
  · subst hij
    simp [Matrix.one_apply_eq]
  · rw [if_neg (sub_ne_zero_of_ne hij)]
    simp [hij]


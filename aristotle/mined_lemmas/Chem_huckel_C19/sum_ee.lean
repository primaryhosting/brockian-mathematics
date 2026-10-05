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

lemma sum_ee : ∑ k : ZMod 19, ee k = 0 := by
  have h : ∑ k : ZMod 19, ee k = ∑ n ∈ Finset.range 19, w19 ^ n := by
    show ∑ k : Fin 19, w19 ^ (k : ℕ) = _
    exact Fin.sum_univ_eq_sum_range (fun n => w19 ^ n) 19
  rw [h, isPrimitiveRoot_w19.geom_sum_eq_zero (by norm_num)]


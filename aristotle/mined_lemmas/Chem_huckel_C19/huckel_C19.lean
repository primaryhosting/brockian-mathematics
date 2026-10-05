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

theorem huckel_C19 :
    spectrum ℂ C19adj =
      {z : ℂ | ∃ k : ℕ, k < 19 ∧ z = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ)} := by
  ext z
  rw [spectrum.mem_iff, Matrix.isUnit_iff_isUnit_det, det_sub, isUnit_iff_ne_zero,
    not_not, Finset.prod_eq_zero_iff]
  constructor
  · rintro ⟨k, -, hk⟩
    refine ⟨k.val, ZMod.val_lt k, ?_⟩
    have : z = mu k := sub_eq_zero.mp hk
    rw [this, mu]
  · rintro ⟨n, hn, rfl⟩
    refine ⟨(n : ZMod 19), Finset.mem_univ _, ?_⟩
    rw [sub_eq_zero, mu, ZMod.val_natCast_of_lt hn]

/-- Auxiliary cancellation lemma. -/

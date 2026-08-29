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

lemma ee_add_ee_neg (k : ZMod 19) : ee k + ee (-k) = mu k := by
  have hcos : ∀ z : ℂ, Complex.exp (z * I) + Complex.exp (-z * I) = 2 * Complex.cos z := by
    intro z
    rw [Complex.cos]
    ring
  have h1 : ee (-k) = Complex.exp (-(2 * Real.pi * k.val / 19 : ℝ) * I) := by
    rw [ee_neg, ee_eq_exp, ← Complex.exp_neg]
    ring_nf
  rw [ee_eq_exp, h1, hcos, mu]
  push_cast
  ring


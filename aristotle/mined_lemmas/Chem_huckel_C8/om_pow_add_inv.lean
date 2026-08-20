/-
# Huckel C 8
Category: Chemistry
Target: Chem.huckel_C8
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede any module docstring, so the header
-- above is a plain block comment; its text is otherwise verbatim.)

import Mathlib

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₈`, indexed by `Fin 8` with cyclic
successor/predecessor. -/

lemma om_pow_add_inv (k : ℕ) :
    om ^ k + om ^ (7 * k) = (2 * Real.cos (2 * Real.pi * k / 8) : ℝ) := by
  have h1 : om ^ k * om ^ (7 * k) = 1 := by
    rw [← pow_add]
    have : k + 7 * k = 8 * k := by ring
    rw [this, pow_mul, om_pow_eight, one_pow]
  have hk : om ^ k = Complex.exp ((2 * Real.pi * k / 8 : ℝ) * Complex.I) := om_pow_eq_exp k
  have h7 : om ^ (7 * k) = Complex.exp (-(2 * Real.pi * k / 8 : ℝ) * Complex.I) := by
    have hne : om ^ k ≠ 0 := by
      rw [hk]; exact Complex.exp_ne_zero _
    have : om ^ (7 * k) = (om ^ k)⁻¹ := by
      field_simp at h1 ⊢
      linear_combination h1
    rw [this, hk, ← Complex.exp_neg]
    ring_nf
  rw [hk, h7, Complex.ofReal_mul, Complex.ofReal_cos]
  norm_num [Complex.two_cos]

/-- The Vandermonde matrix of the powers of `om`; its columns are the eigenvectors. -/

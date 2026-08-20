/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

theorem wch_add_wch_neg (k : ZMod 18) : wch k + wch (-k) = hval k := by
  set t : ℝ := 2 * Real.pi * k.val / 18 with ht
  have h2 : wch k = Complex.exp ((t : ℂ) * Complex.I) := wch_eq_exp k
  have h3 : Complex.exp ((t : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  have hk : wch (-k) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    have h1 := wch_neg_add_self k
    rw [h2] at h1
    rw [Complex.exp_neg]
    field_simp
    linear_combination h1
  rw [h2, hk, hval, ← ht, Complex.ofReal_mul, Complex.ofReal_cos, Complex.cos]
  push_cast
  ring_nf


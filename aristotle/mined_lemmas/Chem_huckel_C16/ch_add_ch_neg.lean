/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not
-- permit a module docstring before the `import` line.)

import Mathlib

namespace Chem

open Finset Complex Matrix

/-- A primitive 16-th root of unity. -/

lemma ch_add_ch_neg (k : ZMod 16) :
    ch k + ch (-k) = 2 * (Real.cos (2 * Real.pi * (k.val : ℝ) / 16) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * (k.val : ℝ) / 16 with hθ
  have hprod : ch k * ch (-k) = 1 := by rw [← ch_add]; simp [ch_zero]
  have hk : ch k = Complex.exp ((θ : ℂ) * Complex.I) := ch_eq_exp k
  have hnk : ch (-k) = Complex.exp (-((θ : ℂ) * Complex.I)) := by
    have hne : Complex.exp ((θ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have : Complex.exp ((θ : ℂ) * Complex.I) * ch (-k)
        = Complex.exp ((θ : ℂ) * Complex.I) * Complex.exp (-((θ : ℂ) * Complex.I)) := by
      rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero, ← hk, hprod]
    exact mul_left_cancel₀ hne this
  rw [hk, hnk, Complex.ofReal_cos, Complex.cos]
  ring_nf

/-- **Hückel theory for the C₁₆ annulene ring.**
The eigenvalues of the adjacency matrix of the cycle graph `C₁₆` are exactly the
sixteen numbers `2 cos (2πk/16)`, `k = 0, …, 15`. -/

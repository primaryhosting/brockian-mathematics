/-
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Hückel theory for the C₁₄ ring

The adjacency eigenvalues of the cycle graph `C₁₄` are exactly the numbers
`2 * cos (2πk/14)` for `k = 0, …, 13`.
-/

namespace Chem

open Finset Complex

/-- A primitive 14-th root of unity. -/

lemma ch_add_ch_neg (k : Fin 14) :
    ch k + ch (-k) = 2 * (Real.cos (2 * Real.pi * (k.val : ℝ) / 14) : ℂ) := by
  set t : ℝ := 2 * Real.pi * (k.val : ℝ) / 14 with ht
  have h1 : ch k = Complex.exp ((t : ℂ) * Complex.I) := by
    rw [ch, om, ← Complex.exp_nat_mul]
    congr 1
    rw [ht]
    push_cast
    ring
  have h2 : ch (-k) = Complex.exp (-((t : ℂ) * Complex.I)) := by
    rw [ch_neg, h1, ← Complex.exp_neg]
  have h3 : Complex.cos (t : ℂ)
      = (Complex.exp ((t : ℂ) * Complex.I) + Complex.exp (-((t : ℂ) * Complex.I))) / 2 := by
    rw [Complex.cos]; ring_nf
  rw [h1, h2, Complex.ofReal_cos, h3]
  ring


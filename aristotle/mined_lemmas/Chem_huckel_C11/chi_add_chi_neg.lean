/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset Complex

noncomputable section

/-- A primitive 11-th root of unity. -/

lemma chi_add_chi_neg (k : Fin 11) :
    chi ((k : ℕ) : ZMod 11) + chi (-((k : ℕ) : ZMod 11))
      = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / 11) : ℝ) : ℂ) := by
  set θ : ℝ := 2 * Real.pi * (k : ℕ) / 11 with hθ
  have hval : (((k : ℕ) : ZMod 11)).val = (k : ℕ) := ZMod.val_natCast_of_lt k.isLt
  have hchi : chi ((k : ℕ) : ZMod 11) = Complex.exp ((θ : ℂ) * Complex.I) := by
    rw [chi, hval, zeta, ← Complex.exp_nat_mul]
    congr 1
    rw [hθ]
    push_cast
    ring
  rw [chi_neg, hchi, ← Complex.exp_neg]
  have : ((2 * Real.cos θ : ℝ) : ℂ) = 2 * Complex.cos (θ : ℂ) := by
    push_cast [Complex.ofReal_cos]
    ring
  rw [this, Complex.two_cos]
  ring_nf

/-- **Hückel theory for the cycle `C₁₁`.**  A complex number `μ` is an eigenvalue of the
adjacency matrix of the cycle graph `C₁₁` if and only if `μ = 2 cos (2πk/11)` for some
`k = 0, 1, …, 10`. -/

/-
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- given as a plain block comment and repeated as a module docstring below.)

import Mathlib

/-!
# Cycle Fiedler Value
Category: Frontier Spectral
Target: Frontier.Spectral.cycle_fiedler_value
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix SimpleGraph Complex ComplexConjugate

namespace Frontier.Spectral

/-! ## A discrete additive character on `ZMod N` -/

section Character

variable {N : ℕ}

/-- The primitive `N`-th root of unity `exp (2πi/N)`. -/

lemma fiedlerVec_eigen (i : ZMod (m + 3)) :
    2 * fiedlerVec m i - fiedlerVec m (i - 1) - fiedlerVec m (i + 1)
      = (2 - 2 * Real.cos (2 * Real.pi / (m + 3))) * fiedlerVec m i := by
  have hc1 : (chi (m + 3) 1).re = Real.cos (2 * Real.pi / (m + 3)) := by
    rw [chi_re, val_one_zmod]
    norm_num
  have hsum : chi (m + 3) (i - 1) + chi (m + 3) (i + 1)
      = chi (m + 3) i * ((2 * (chi (m + 3) 1).re : ℝ) : ℂ) := by
    have e1 : chi (m + 3) (i - 1) = chi (m + 3) i * chi (m + 3) (-1) := by
      rw [← chi_add]; congr 1; ring
    have e2 : chi (m + 3) (i + 1) = chi (m + 3) i * chi (m + 3) 1 := chi_add i 1
    rw [e1, e2, ← chi_conj, ← mul_add, add_comm (conj _) _]
    congr 1
    exact Complex.add_conj _
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero] at hre
  simp only [fiedlerVec]
  rw [← hc1]
  linarith [hre]


/-
# Qft Unitary 6
Category: Quantum Computing
Target: QC.qft_unitary_6
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The requested header is reproduced verbatim above; it is written as a plain block
-- comment rather than a `/-!` module docstring because Lean 4 does not allow a module
-- docstring to precede the `import` line.)

import Mathlib

namespace QC

open Complex Finset
open scoped Matrix

/-- The `n × n` quantum Fourier transform matrix: the entry in row `j`, column `k` is
`exp(2πi·j·k/n) / √n`. -/

lemma entry_mul_conj (n : ℕ) (j k l : Fin n) :
    qftMatrix n j l * (starRingEnd ℂ) (qftMatrix n k l) = (qftRatio n j k) ^ (l : ℕ) / n := by
  have hs : ((Real.sqrt n : ℝ) : ℂ) * ((Real.sqrt n : ℝ) : ℂ) = (n : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp
  unfold qftMatrix qftRatio
  rw [← Complex.exp_nat_mul, map_div₀, ← Complex.exp_conj, Complex.conj_ofReal,
    div_mul_div_comm, hs, ← Complex.exp_add]
  have hc : ((starRingEnd ℂ) (2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) * (l : ℕ) : ℕ) : ℂ) / n))
      = -(2 * (Real.pi : ℂ) * Complex.I * (((k : ℕ) * (l : ℕ) : ℕ) : ℂ) / n) := by
    simp [map_div₀, Complex.conj_ofReal, map_ofNat]
    ring
  rw [hc]
  congr 2
  push_cast
  ring

/-- `qftRatio n j k` is an `n`-th root of unity. -/

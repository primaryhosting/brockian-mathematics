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

lemma qftRatio_pow_n (n : ℕ) (hn : 0 < n) (j k : Fin n) : (qftRatio n j k) ^ n = 1 := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  unfold qftRatio
  rw [← Complex.exp_nat_mul, Complex.exp_eq_one_iff]
  refine ⟨(j : ℕ) - (k : ℕ), ?_⟩
  push_cast
  field_simp

/-- `qftRatio n j k` equals `1` exactly on the diagonal. -/

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

lemma qftRatio_eq_one_iff (n : ℕ) (hn : 0 < n) (j k : Fin n) :
    qftRatio n j k = 1 ↔ j = k := by
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  constructor
  · intro h
    unfold qftRatio at h
    rw [Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    have hpi : (Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
    field_simp at hm
    have h2 : ((j : ℕ) : ℂ) - ((k : ℕ) : ℂ) = (m : ℂ) * (n : ℂ) := by linear_combination hm
    have h3 : ((j : ℕ) : ℤ) - ((k : ℕ) : ℤ) = m * (n : ℤ) := by exact_mod_cast h2
    have hj := j.isLt
    have hk := k.isLt
    have hm0 : m = 0 := by
      rcases lt_trichotomy m 0 with h0 | h0 | h0
      · exfalso
        have : m * (n : ℤ) ≤ -(n : ℤ) := by nlinarith
        omega
      · exact h0
      · exfalso
        have : (n : ℤ) ≤ m * (n : ℤ) := by nlinarith
        omega
    rw [hm0] at h3
    simp at h3
    exact Fin.ext (by omega)
  · rintro rfl
    unfold qftRatio
    simp

/-- The `n × n` QFT matrix satisfies `U * Uᴴ = 1` for every `n > 0`. -/

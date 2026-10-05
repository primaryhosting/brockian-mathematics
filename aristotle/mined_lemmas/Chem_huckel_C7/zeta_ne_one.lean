/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem zeta_ne_one : zeta ≠ 1 := by
  intro h
  rw [zeta, Complex.exp_eq_one_iff] at h
  obtain ⟨n, hn⟩ := h
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h2 : ((7 * n - 1 : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) = 0 := by
    push_cast
    linear_combination (-7 : ℂ) * hn
  rcases mul_eq_zero.1 h2 with h3 | h3
  · have : (7 * n - 1 : ℤ) = 0 := by exact_mod_cast h3
    omega
  · simp [hpi, Complex.I_ne_zero] at h3


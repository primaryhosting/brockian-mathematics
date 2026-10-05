import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem chi_neg (k : ZMod 10) : chi (-k) = (chi k)⁻¹ := by
  have h := chi_add k (-k)
  simp [chi_zero] at h
  exact eq_inv_of_mul_eq_one_left (by rw [mul_comm]; exact h.symm)


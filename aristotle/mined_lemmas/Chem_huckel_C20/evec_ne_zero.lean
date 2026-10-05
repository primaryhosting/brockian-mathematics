import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

lemma evec_ne_zero (k : ℕ) : evec k ≠ 0 := by
  intro h
  have h0 : evec k 0 = 0 := by rw [h]; rfl
  rw [evec] at h0
  simp at h0


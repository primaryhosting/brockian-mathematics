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

lemma w_ne_zero : w ≠ 0 := by
  intro h
  have h20 := w_pow_20
  rw [h] at h20
  simp at h20


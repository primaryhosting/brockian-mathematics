import Mathlib

/-!
# Huckel C 15
Category: Chemistry
Target: Chem.huckel_C15
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset SimpleGraph

/-- A primitive 15-th root of unity. -/

lemma g_sub_one (i : Fin 15) : g (i - 1) = g i * zeta⁻¹ := by
  have h := g_add (i - 1) 1
  rw [sub_add_cancel, g_one] at h
  rw [h, mul_assoc, mul_inv_cancel₀ zeta_ne_zero, mul_one]


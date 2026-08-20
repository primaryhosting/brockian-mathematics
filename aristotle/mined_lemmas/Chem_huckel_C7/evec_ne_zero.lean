import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/

lemma evec_ne_zero (k : Fin 7) : evec k ≠ 0 := by
  intro h
  have h0 := congrFun h 0
  simp only [evec, Pi.zero_apply, zero_mul] at h0
  exact ee_ne_zero 0 h0

/-- Fourier inversion on `Fin 7`. -/

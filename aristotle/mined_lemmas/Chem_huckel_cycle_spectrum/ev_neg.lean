/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Polynomial Matrix SimpleGraph Finset

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma ev_neg (a : Fin n) : ev (-a) = (ev a)⁻¹ := by
  have h : ev a * ev (-a) = 1 := by rw [← ev_add, add_neg_cancel, ev_zero]
  field_simp [ev_ne_zero a] at h ⊢
  linear_combination h


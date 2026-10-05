import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex SimpleGraph Matrix

/-- The primitive `n`-th root of unity `exp (2πi/n)`. -/

lemma pred_ne_succ {N : ℕ} (j : Fin (N + 3)) : (j - 1 : Fin (N + 3)) ≠ j + 1 := by
  intro h
  rw [sub_eq_iff_eq_add, add_assoc] at h
  have h2 : ((1 : Fin (N + 3)) + 1) = 0 := left_eq_add.mp h
  have : ((1 : Fin (N + 3)) + 1 : Fin (N + 3)).val = 0 := by rw [h2]; rfl
  rw [Fin.val_add, Fin.val_one, Nat.mod_eq_of_lt (by omega : 1 + 1 < N + 3)] at this
  omega

/-- Key computation: the adjacency matrix acts on the Fourier basis diagonally. -/

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

lemma succ_val_modEq {N : ℕ} (j : Fin (N + 2)) :
    ((j + 1 : Fin (N + 2)) : ℕ) ≡ (j : ℕ) + 1 [MOD (N + 2)] := by
  rw [Fin.val_add, Fin.val_one]
  exact Nat.mod_modEq _ _


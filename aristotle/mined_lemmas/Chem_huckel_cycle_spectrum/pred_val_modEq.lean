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

lemma pred_val_modEq {N : ℕ} (j : Fin (N + 2)) :
    ((j - 1 : Fin (N + 2)) : ℕ) + 1 ≡ (j : ℕ) [MOD (N + 2)] := by
  have h : ((j - 1 : Fin (N + 2)) + 1 : Fin (N + 2)) = j := by
    rw [sub_add_cancel]
  have := congrArg Fin.val h
  rw [Fin.val_add, Fin.val_one] at this
  calc ((j - 1 : Fin (N + 2)) : ℕ) + 1
      ≡ (((j - 1 : Fin (N + 2)) : ℕ) + 1) % (N + 2) [MOD (N + 2)] := (Nat.mod_modEq _ _).symm
    _ = (j : ℕ) := this


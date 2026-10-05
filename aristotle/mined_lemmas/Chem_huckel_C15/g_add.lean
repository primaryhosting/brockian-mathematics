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

lemma g_add (x y : Fin 15) : g (x + y) = g x * g y := by
  unfold g
  rw [Fin.val_add, zeta_pow_modEq (Nat.mod_modEq _ _), pow_add]


/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- A primitive 11-th root of unity. -/

lemma eps_add (x y : ZMod 11) : eps (x + y) = eps x * eps y := by
  rw [eps, eps, eps, ← pow_add]
  refine zeta_pow_congr ?_
  rw [ZMod.val_add]
  simp [Nat.mod_mod_of_dvd]


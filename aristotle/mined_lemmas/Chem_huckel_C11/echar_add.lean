/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open Complex Polynomial

namespace Chem

/-- A primitive 11-th root of unity. -/

lemma echar_add (x y : Fin 11) : echar (x + y) = echar x * echar y := by
  rw [echar, echar, echar, ← pow_add]
  exact zeta11_pow_congr (by simp [Fin.val_add, Nat.add_mod])


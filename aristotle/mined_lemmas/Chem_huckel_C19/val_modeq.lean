/-
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

open scoped BigOperators Real

namespace Chem

open Complex Matrix Finset

/-- A primitive 19-th root of unity. -/

lemma val_modeq (i : ZMod 19) (c : ℕ) : (i + (c : ZMod 19)).val ≡ i.val + c [MOD 19] := by
  rw [Nat.ModEq, ZMod.val_add, ZMod.val_natCast]
  omega


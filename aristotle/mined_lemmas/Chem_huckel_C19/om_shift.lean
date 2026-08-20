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

lemma om_shift (i : ZMod 19) (c m : ℕ) :
    om ^ ((i + (c : ZMod 19)).val * m) = om ^ ((i.val + c) * m) :=
  om_pow_congr (Nat.ModEq.mul_right m (val_modeq i c))

/-- The eigenvalue equation `A · V = V · diag(λ)`. -/

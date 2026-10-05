/-
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open scoped Real
open Finset

instance : Fact (Nat.Prime 17) := ⟨by norm_num⟩

/-- A primitive 17-th root of unity. -/

lemma ee_natCast (k : ℕ) : ee (k : ZMod 17) = om ^ k := by
  rw [ee]
  exact om_pow_congr (by simp [ZMod.val_natCast])

/-- Orthogonality of the characters. -/

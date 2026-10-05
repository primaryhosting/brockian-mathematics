/-
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex

/-- The adjacency matrix of the cycle graph `C₇`, indexed by `ZMod 7`:
vertices `i` and `j` are adjacent iff they differ by `1` modulo `7`. -/

theorem fourierVec_add (k : ℕ) (a b : ZMod 7) :
    fourierVec k (a + b) = fourierVec k a * fourierVec k b := by
  have h : (a + b).val ≡ a.val + b.val [MOD 7] := by
    rw [ZMod.val_add]; exact Nat.mod_mod _ _
  have h2 : k * (a + b).val ≡ k * a.val + k * b.val [MOD 7] :=
    calc k * (a + b).val ≡ k * (a.val + b.val) [MOD 7] := Nat.ModEq.mul_left k h
      _ = k * a.val + k * b.val := by ring
  rw [fourierVec, fourierVec, fourierVec, ← pow_add]
  exact zeta_pow_congr h2


/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not
-- permit a module docstring before the `import` line.)

import Mathlib

namespace Chem

open Finset Complex Matrix

/-- A primitive 16-th root of unity. -/

lemma ch_ne_one {m : ZMod 16} (hm : m ≠ 0) : ch m ≠ 1 := by
  intro h
  have hdvd : (16 : ℕ) ∣ m.val := (zeta16_primitive.pow_eq_one_iff_dvd m.val).1 h
  have hlt : m.val < 16 := m.val_lt
  have hpos : m.val ≠ 0 := fun h0 => hm ((ZMod.val_eq_zero m).1 h0)
  exact absurd (Nat.le_of_dvd (Nat.pos_of_ne_zero hpos) hdvd) (by omega)

/-- Orthogonality of characters on `ZMod 16`. -/

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

lemma C16_mulVec_ch (k : ZMod 16) :
    C16 *ᵥ (fun j => ch (k * j)) = (ch k + ch (-k)) • (fun j => ch (k * j)) := by
  funext i
  rw [C16_mulVec]
  have h1 : k * (i - 1) = k * i + (-k) := by ring
  have h2 : k * (i + 1) = k * i + k := by ring
  simp only [h1, h2, ch_add, Pi.smul_apply, smul_eq_mul]
  ring


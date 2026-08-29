/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 does not permit a module docstring `/-! ... -/` before the `import`
line, so the required header appears here as an ordinary block comment.)
-/

import Mathlib

namespace Chem

open Complex Matrix

/-! ### The primitive 20-th root of unity and the associated character -/

/-- The primitive 20-th root of unity `exp (2πi/20)`. -/

lemma e_add (a b : ZMod 20) : e (a + b) = e a * e b := by
  rw [e, e, e, ← pow_add]
  exact om_pow_congr (by rw [ZMod.val_add, Nat.mod_mod])


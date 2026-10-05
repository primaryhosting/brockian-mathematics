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

lemma e_neg (k : ZMod 20) : e (-k) = om ^ (19 * k.val) := by
  have h20 : (20 : ZMod 20) = 0 := by decide
  have hk : (-k) = 19 * k := by linear_combination (-k) * h20
  rw [hk, e, ZMod.val_mul, show ((19 : ZMod 20)).val = 19 from rfl]
  exact om_pow_congr (by rw [Nat.mod_mod])

/-! ### The cycle graph `C₂₀` and its adjacency matrix -/

/-- The adjacency matrix of the cycle graph `C₂₀`, with vertices indexed by `ZMod 20`:
`i` and `j` are adjacent iff they differ by `1`. -/

import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the header block above sits immediately after the single import.)

namespace Frontier

/-! ## Definitions -/

/-- `a : ℤ` is a *primitive root* modulo `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/

theorem isPrimitiveRootMod_neg_one_two : IsPrimitiveRootMod (-1) 2 := by
  show orderOf (((-1 : ℤ)) : ZMod 2) = 1
  have h : (((-1 : ℤ)) : ZMod 2) = 1 := by decide
  rw [h, orderOf_one]

/-- The exceptional set for `a = -1` computed exactly: `-1` is a primitive root modulo `p`
precisely for `p = 2` and `p = 3`. -/

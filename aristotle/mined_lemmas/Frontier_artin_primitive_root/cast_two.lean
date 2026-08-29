/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

set_option maxRecDepth 100000

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue class generates the
multiplicative group of `ZMod p`, i.e. its multiplicative order is `p - 1`. -/

private theorem cast_two (p : ℕ) : ((2 : ℤ) : ZMod p) = 2 := by push_cast; ring


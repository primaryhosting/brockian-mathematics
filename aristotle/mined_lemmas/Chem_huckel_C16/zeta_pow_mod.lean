import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header block is placed immediately after `import Mathlib`, since Lean 4 requires
-- `import` commands to come first in a file.)

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Finset

/-- A primitive 16-th root of unity. -/

lemma zeta_pow_mod (a : ℕ) : zeta ^ (a % 16) = zeta ^ a := by
  conv_rhs => rw [← Nat.div_add_mod a 16]
  rw [pow_add, pow_mul, zeta_pow_16, one_pow, one_mul]


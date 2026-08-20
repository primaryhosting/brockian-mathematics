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

lemma ee_add_ee_neg (k : ZMod 16) : ee k + ee (-k) = evC16 k := by
  rw [ee_neg, ee_eq_exp, evC16, ← Complex.exp_neg, Complex.ofReal_cos, Complex.two_cos, neg_mul]


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

lemma ee_neg (k : ZMod 16) : ee (-k) = (ee k)⁻¹ := by
  have h : ee k * ee (-k) = 1 := by rw [← ee_add, add_neg_cancel, ee_zero]
  field_simp [ee_ne_zero k]
  linear_combination h


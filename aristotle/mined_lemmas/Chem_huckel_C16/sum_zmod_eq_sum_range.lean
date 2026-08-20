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

lemma sum_zmod_eq_sum_range (f : ℕ → ℂ) :
    ∑ j : ZMod 16, f j.val = ∑ t ∈ Finset.range 16, f t := by
  rw [← Fin.sum_univ_eq_sum_range]
  rfl

/-- Orthogonality of the characters. -/

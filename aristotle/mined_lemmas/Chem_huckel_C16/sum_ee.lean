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

lemma sum_ee (d : ZMod 16) :
    ∑ j : ZMod 16, ee (j * d) = if d = 0 then 16 else 0 := by
  have hterm : ∀ j : ZMod 16, ee (j * d) = ee d ^ j.val := by
    intro j
    rw [← ee_natCast_mul j.val d, ZMod.natCast_zmod_val]
  rw [Finset.sum_congr rfl (fun j _ => hterm j),
    sum_zmod_eq_sum_range (fun t => ee d ^ t)]
  by_cases hd : d = 0
  · subst hd
    simp [ee_zero]
  · have hne : ee d ≠ 1 := fun h => hd ((ee_eq_one_iff d).1 h)
    rw [geom_sum_eq hne, ee_pow_16, if_neg hd]
    simp

/-- The adjacency matrix of the cycle graph `C₁₆`, indexed by `ZMod 16`. -/

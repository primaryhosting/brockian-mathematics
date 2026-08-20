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

lemma dftQ_mul_dftP : dftQ * dftP = 1 := by
  ext i k
  rw [Matrix.mul_apply]
  have hterm : ∀ j : ZMod 16, dftQ i j * dftP j k = (16 : ℂ)⁻¹ * ee (j * (k - i)) := by
    intro j
    have harg : -(i * j) + j * k = j * (k - i) := by ring
    simp only [dftQ, dftP, Matrix.of_apply, mul_assoc, ← ee_add, harg]
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, sum_ee, Matrix.one_apply]
  by_cases h : k = i
  · subst h; norm_num
  · rw [if_neg (sub_ne_zero.2 h), if_neg (Ne.symm h)]
    ring


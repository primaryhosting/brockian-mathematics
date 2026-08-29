import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

theorem sum_zmod_range (g : ℕ → ℂ) : ∑ k : ZMod 10, g k.val = ∑ i ∈ Finset.range 10, g i := by
  refine Finset.sum_nbij' (i := fun k => ZMod.val k) (j := fun n => (n : ZMod 10)) ?_ ?_ ?_ ?_ ?_ <;>
    intros <;> simp_all [ZMod.val_lt, Finset.mem_range, ZMod.natCast_val, ZMod.cast_id]

/-- Orthogonality of the characters of `ZMod 10`. -/

import Mathlib

/-!
# Huckel C 13
Category: Chemistry
Target: Chem.huckel_C13
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

/-- The adjacency matrix of the cycle graph `C₁₃`, with vertices indexed by `ZMod 13`:
vertex `i` is adjacent exactly to `i + 1` and `i - 1`. -/

lemma sum_zmod_val (f : ℕ → ℂ) : ∑ k : ZMod 13, f k.val = ∑ j ∈ Finset.range 13, f j := by
  refine Finset.sum_nbij' (fun k => k.val) (fun j => (j : ZMod 13)) ?_ ?_ ?_ ?_ ?_
  · intro a _; simp [Finset.mem_range, ZMod.val_lt]
  · intro a _; simp
  · intro a _; simp [ZMod.natCast_val, ZMod.cast_id]
  · intro a ha; simp only [Finset.mem_range] at ha; exact ZMod.val_cast_of_lt ha
  · intro a _; rfl

/-- The sum of the character over all of `ZMod 13` vanishes. -/

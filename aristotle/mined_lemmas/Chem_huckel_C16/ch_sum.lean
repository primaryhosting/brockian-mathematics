/-
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 does not
-- permit a module docstring before the `import` line.)

import Mathlib

namespace Chem

open Finset Complex Matrix

/-- A primitive 16-th root of unity. -/

lemma ch_sum (m : ZMod 16) : ∑ k : ZMod 16, ch (k * m) = if m = 0 then 16 else 0 := by
  by_cases hm : m = 0
  · subst hm
    simp [ch_zero]
  · simp only [hm, if_false]
    have hre : ∑ k : ZMod 16, ch m ^ (ZMod.val k) = ∑ i ∈ Finset.range 16, ch m ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => ch m ^ i) 16
    have : ∑ k : ZMod 16, ch (k * m) = ∑ i ∈ Finset.range 16, ch m ^ i := by
      rw [← hre]
      exact Finset.sum_congr rfl fun k _ => ch_mul k m
    rw [this, geom_sum_eq (ch_ne_one hm), ch_pow16, sub_self, zero_div]

/-- The adjacency matrix of the cycle graph `C₁₆`, with vertices indexed by `ZMod 16`:
two vertices are adjacent exactly when they differ by `1`. -/

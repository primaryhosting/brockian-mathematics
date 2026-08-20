/-
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- The Hückel (adjacency) matrix of the cycle graph `C n`, with vertices indexed by `ZMod n`:
vertex `i` is joined to `i + 1` and to `i - 1`.  For `n ≥ 3` this is exactly the adjacency matrix
of the simple cycle graph `C n`; for `n = 1, 2` it is the circulant matrix `S + S⁻¹` (`S` the
cyclic shift), which is the convention under which the Hückel spectrum formula holds. -/

lemma sum_zmod_eq_sum_range (n : ℕ) [NeZero n] (f : ZMod n → ℂ) :
    ∑ a : ZMod n, f a = ∑ m ∈ Finset.range n, f (m : ZMod n) := by
  refine Finset.sum_nbij' (fun a => ZMod.val a) (fun m => (m : ZMod n)) ?_ ?_ ?_ ?_ ?_
  · intro a _; simp [ZMod.val_lt]
  · intro m _; simp
  · intro a _; simp
  · intro m hm; simp only [Finset.mem_range] at hm; exact ZMod.val_cast_of_lt hm
  · intro a _; rw [ZMod.natCast_rightInverse.leftInverse]

/-- Orthogonality relation for the character `chi`. -/

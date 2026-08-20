import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Finset Matrix

namespace Chem

/-- The adjacency matrix of the cycle graph `C₁₁`, with vertices indexed by `ZMod 11`:
vertex `i` is adjacent to `i + 1` and `i - 1`. -/

lemma sum_ch_mul (t : ZMod 11) :
    ∑ i : ZMod 11, ch (t * i) = if t = 0 then (11 : ℂ) else 0 := by
  split_ifs with h
  · simp [h, Finset.card_univ]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 11 h)

/-- The (unnormalised) discrete Fourier matrix. -/

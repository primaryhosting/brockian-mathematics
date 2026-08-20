import Mathlib
/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix

/-- The adjacency matrix of the cycle graph `C₁₈`, with vertices indexed by `ZMod 18`:
two vertices are adjacent iff they differ by `1` modulo `18`. -/

lemma w_sum (b : ZMod 18) :
    ∑ x : ZMod 18, w (x * b) = if b = 0 then (18 : ℂ) else 0 := by
  have := AddChar.sum_mulShift (R := ZMod 18) (R' := ℂ) b (ZMod.isPrimitive_stdAddChar 18)
  simpa [w] using this


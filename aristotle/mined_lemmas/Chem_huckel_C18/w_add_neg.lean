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

lemma w_add_neg (k : ZMod 18) :
    w k + w (-k) = ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ) := by
  rw [w_val, w_neg]
  push_cast
  rw [Complex.cos]
  have h : (2 : ℂ) * (Real.pi : ℂ) * I * (k.val : ℂ) / 18
      = (2 * (Real.pi : ℂ) * (k.val : ℂ) / 18) * I := by ring
  rw [h]
  ring_nf


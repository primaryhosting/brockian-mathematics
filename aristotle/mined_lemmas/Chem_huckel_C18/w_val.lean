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

lemma w_val (k : ZMod 18) : w k = Complex.exp (2 * Real.pi * I * (k.val : ℂ) / 18) := by
  have hk : ((k.val : ℤ) : ZMod 18) = k := by simp
  calc w k = ZMod.stdAddChar (((k.val : ℤ) : ZMod 18)) := by rw [hk]; rfl
    _ = Complex.exp (2 * Real.pi * I * ((k.val : ℤ) : ℂ) / 18) := ZMod.stdAddChar_coe _
    _ = Complex.exp (2 * Real.pi * I * (k.val : ℂ) / 18) := by push_cast; ring_nf


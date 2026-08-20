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

def C18adj : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.of fun i j => if j = i + 1 ∨ j = i - 1 then 1 else 0

/-- `C18adj` is the adjacency matrix of Mathlib's cycle graph on `Fin 18`
(note that `ZMod 18` and `Fin 18` are the same type). -/

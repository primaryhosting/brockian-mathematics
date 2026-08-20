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

noncomputable def Gmat : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.of fun k j => (18 : ℂ)⁻¹ * w (-(k * j))

/-- The diagonal matrix of Hückel eigenvalues `2 cos (2πk/18)`. -/

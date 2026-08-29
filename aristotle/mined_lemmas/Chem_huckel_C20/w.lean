import Mathlib

/-!
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset Matrix

/-- A primitive 20-th root of unity. -/

noncomputable def w : ℂ := Complex.exp (2 * Real.pi * Complex.I / 20)

/-- The adjacency matrix of the cycle graph `C₂₀` (Mathlib's `SimpleGraph.cycleGraph 20`),
with vertices indexed by `ZMod 20`: two vertices are adjacent iff they differ by `1` mod `20`. -/

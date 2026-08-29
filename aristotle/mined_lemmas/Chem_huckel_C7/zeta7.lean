import Mathlib

/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

/-- Adjacency matrix of the cycle graph `C₇`, with vertices indexed by `ZMod 7`:
vertex `i` is adjacent to `i + 1` and to `i - 1`. -/

noncomputable def zeta7 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)


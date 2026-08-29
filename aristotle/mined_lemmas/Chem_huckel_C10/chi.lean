import Mathlib

/-!
# Huckel C 10
Category: Chemistry
Target: Chem.huckel_C10
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Complex Real Matrix Finset

namespace Chem

/-- A primitive 10-th root of unity. -/

noncomputable def chi (n : ZMod 10) : ℂ := om ^ n.val

/-- Adjacency matrix of the cycle graph `C₁₀`, with vertices indexed by `ZMod 10`:
vertices `i` and `j` are adjacent exactly when `i - j = ±1`. -/

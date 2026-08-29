import Mathlib

/-!
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Real Matrix Finset

/-- A primitive 18-th root of unity. -/

noncomputable def Dg : Matrix (ZMod 18) (ZMod 18) ℂ :=
  Matrix.diagonal fun k => ((2 * Real.cos (2 * Real.pi * k.val / 18) : ℝ) : ℂ)


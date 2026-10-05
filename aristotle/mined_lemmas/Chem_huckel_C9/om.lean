import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Matrix Finset

noncomputable section

/-- A primitive 9-th root of unity. -/

noncomputable def om : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

/-- The additive character `ZMod 9 → ℂ`, `a ↦ ω ^ a`. -/

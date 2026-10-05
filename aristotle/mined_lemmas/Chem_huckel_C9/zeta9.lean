import Mathlib

/-!
# Huckel C 9
Category: Chemistry
Target: Chem.huckel_C9
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Complex Finset

/-- A primitive ninth root of unity. -/

noncomputable def zeta9 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 9)

/-- The additive character `ZMod 9 → ℂ`, `x ↦ ζ₉ ^ x`. -/

import Mathlib
/-!
# Huckel C 7
Category: Chemistry
Target: Chem.huckel_C7
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators Real

namespace Chem

open Complex Finset Matrix

/-- A primitive 7-th root of unity. -/

noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / 7)


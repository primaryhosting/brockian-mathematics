/-
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Huckel C 5
Category: Chemistry
Target: Chem.huckel_C5
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Finset Matrix

namespace Chem

/-- A primitive fifth root of unity. -/

noncomputable def zeta5 : ℂ := Complex.exp (2 * Real.pi * Complex.I / 5)

/-- The character `m ↦ ζ₅ ^ m` of `ZMod 5`. -/

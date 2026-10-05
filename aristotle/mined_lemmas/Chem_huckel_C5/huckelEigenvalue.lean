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

noncomputable def huckelEigenvalue (k : ZMod 5) : ℂ :=
  2 * Real.cos (2 * Real.pi * k.val / 5)

/-- The adjacency matrix of `C₅` is symmetric. -/

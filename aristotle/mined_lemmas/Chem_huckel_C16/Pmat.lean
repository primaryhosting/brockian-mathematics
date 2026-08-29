import Mathlib

/-!
# Huckel C 16
Category: Chemistry
Target: Chem.huckel_C16
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix Finset

/-- A primitive 16-th root of unity. -/

noncomputable def Pmat : Matrix (ZMod 16) (ZMod 16) ℂ :=
  Matrix.vandermonde (fun j : ZMod 16 => zeta ^ j.val)


/-
# Huckel C 18
Category: Chemistry
Target: Chem.huckel_C18
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Matrix Polynomial Finset

noncomputable section

/-- A primitive 18-th root of unity. -/

def Pmat : Matrix (ZMod 18) (ZMod 18) ℂ := fun j k => wch (j * k)

/-- Its inverse. -/

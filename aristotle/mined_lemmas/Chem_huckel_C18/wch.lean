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

def wch (a : ZMod 18) : ℂ := zeta ^ a.val

/-- The adjacency matrix of the cycle graph `C₁₈`, indexed by `ZMod 18`. -/

/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Complex Finset

/-- A primitive 11-th root of unity. -/

noncomputable def eps (x : ZMod 11) : ℂ := zeta ^ x.val

/-- The adjacency matrix of the cycle graph `C₁₁`, indexed by `ZMod 11`. -/

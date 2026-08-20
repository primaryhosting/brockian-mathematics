/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

open Finset Complex

noncomputable section

/-- A primitive 11-th root of unity. -/

noncomputable def chi (x : ZMod 11) : ℂ := zeta ^ x.val

/-- The adjacency matrix of the cycle graph `C₁₁`, as a circulant matrix indexed by
`ZMod 11`: vertices `i` and `j` are adjacent iff `i - j = ±1`. -/

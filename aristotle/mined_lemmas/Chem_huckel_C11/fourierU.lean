/-
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Huckel C 11
Category: Chemistry
Target: Chem.huckel_C11
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Complex Finset

namespace Chem

/-- The circulant form of the adjacency matrix of the cycle graph `C₁₁`,
with vertices indexed by `ZMod 11`. -/

noncomputable def fourierU : (Matrix (ZMod 11) (ZMod 11) ℂ)ˣ :=
  ⟨fourierP, fourierQ, fourierP_mul_fourierQ, fourierQ_mul_fourierP⟩

/-- The columns of the Fourier matrix diagonalise the adjacency matrix. -/

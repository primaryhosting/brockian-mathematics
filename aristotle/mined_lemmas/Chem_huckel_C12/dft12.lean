import Mathlib

/-!
# Huckel C 12
Category: Chemistry
Target: Chem.huckel_C12
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real

set_option maxHeartbeats 1000000

namespace Chem

open Complex Polynomial Matrix Finset

/-- The primitive 12-th root of unity `exp(2πi/12)`. -/

noncomputable def dft12 : Matrix (ZMod 12) (ZMod 12) ℂ := fun j k => zeta12 (j * k)

/-- The inverse of the discrete Fourier transform matrix. -/

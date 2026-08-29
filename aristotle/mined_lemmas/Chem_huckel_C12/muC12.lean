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

noncomputable def muC12 (k : ZMod 12) : ℝ := 2 * Real.cos (2 * Real.pi * k.val / 12)


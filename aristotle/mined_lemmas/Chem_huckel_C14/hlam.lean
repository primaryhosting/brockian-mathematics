import Mathlib

/-!
# Huckel C 14
Category: Chemistry
Target: Chem.huckel_C14
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Finset Complex

set_option maxHeartbeats 1000000

namespace Chem

/-- A primitive 14-th root of unity. -/

noncomputable def hlam (k : Fin 14) : ℂ := ((2 * Real.cos (2 * Real.pi * k / 14) : ℝ) : ℂ)


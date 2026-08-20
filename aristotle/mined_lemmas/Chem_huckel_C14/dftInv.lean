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

noncomputable def dftInv : Matrix (Fin 14) (Fin 14) ℂ := fun k i => (14 : ℂ)⁻¹ * (chi (k * i))⁻¹


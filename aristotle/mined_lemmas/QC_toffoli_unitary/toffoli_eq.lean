/-
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Toffoli Unitary
Category: Quantum Computing
Target: QC.toffoli_unitary
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Equiv

/-- The permutation of the computational basis `|abc⟩` (indexed by `Fin 8` via
`i = 4a + 2b + c`) realized by the Toffoli (CCNOT) gate: it flips the target bit
exactly on the two basis states `|110⟩ = 6` and `|111⟩ = 7`. -/

theorem toffoli_eq : toffoli =
    !![1, 0, 0, 0, 0, 0, 0, 0;
       0, 1, 0, 0, 0, 0, 0, 0;
       0, 0, 1, 0, 0, 0, 0, 0;
       0, 0, 0, 1, 0, 0, 0, 0;
       0, 0, 0, 0, 1, 0, 0, 0;
       0, 0, 0, 0, 0, 1, 0, 0;
       0, 0, 0, 0, 0, 0, 0, 1;
       0, 0, 0, 0, 0, 0, 1, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toffoli, toffoliPerm, Equiv.swap_apply_def]

/-- The Toffoli matrix is its own inverse. -/

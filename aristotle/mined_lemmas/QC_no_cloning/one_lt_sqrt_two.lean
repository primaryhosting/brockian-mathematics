/-
/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
-- (The header above is reproduced verbatim as the module docstring below; Lean requires
-- `import` commands to precede any docstring command.)

import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QC

/-- The state space of a single qubit, `H = ℂ²` with its standard inner product. -/
abbrev Qubit : Type := EuclideanSpace ℂ (Fin 2)

/-- The state space of a pair of qubits, `H ⊗ H ≅ ℂ² ⊗ ℂ² ≅ ℂ^(2×2)`. -/
abbrev TwoQubit : Type := EuclideanSpace ℂ (Fin 2 × Fin 2)

/-- The tensor (Kronecker) product of two qubit states: `(u ⊗ v) (i, j) = u i * v j`. -/

theorem one_lt_sqrt_two : 1 < Real.sqrt 2 := by
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  nlinarith [Real.sqrt_nonneg 2, hs]

/-- **No-cloning theorem.** There is no unitary operator `U` on `H ⊗ H` (with `H = ℂ²`) such
that `U (|ψ⟩ ⊗ |0⟩) = |ψ⟩ ⊗ |ψ⟩` for every state (unit vector) `|ψ⟩`. -/

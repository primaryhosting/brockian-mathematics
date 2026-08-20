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

theorem inner_ket0_ketPlus : inner ℂ ket0 ketPlus = ((Real.sqrt 2)⁻¹ : ℝ) := by
  simp [ket0, ketPlus, PiLp.inner_apply, RCLike.inner_apply, Fin.sum_univ_two]

/-- **No cloning, abstract form.** Let `H` and `E` be complex inner product spaces and let
`ten : H → H → E` be a "tensor product" pairing, i.e. one satisfying
`⟪a ⊗ b, c ⊗ d⟫ = ⟪a, c⟫ * ⟪b, d⟫`. If `H` contains two states `u`, `v` whose overlap
`⟪u, v⟫` is neither `0` nor `1` (i.e. they are neither orthogonal nor equal up to phase),
then no unitary `U` on `E` can clone: `U (ψ ⊗ e₀) = ψ ⊗ ψ` cannot hold for all states `ψ`.

The proof is the standard one: unitaries preserve inner products, so the overlap `c = ⟪u, v⟫`
would satisfy `c * c = c`, forcing `c ∈ {0, 1}`. -/

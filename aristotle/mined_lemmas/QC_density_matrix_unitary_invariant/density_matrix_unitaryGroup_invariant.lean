import Mathlib
/-!
# Density Matrix Unitary Invariant
Category: Quantum Computing
Target: QC.density_matrix_unitary_invariant
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` lines to precede every command, including module
-- docstrings, so the required header comment appears immediately after the import.

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise
open scoped Matrix
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QC

/-- **Density matrices are preserved by unitary conjugation.**

If `ρ` is a density matrix (positive semidefinite with unit trace) and `U` is unitary
then `U * ρ * Uᴴ` is again a density matrix. Only the isometry condition `Uᴴ * U = 1`
is needed.

The positive-semidefiniteness part is `Matrix.PosSemidef.mul_mul_conjTranspose_same`
from Mathlib; the trace part follows from cyclicity of the trace
(`Matrix.trace_mul_cycle`). -/

theorem density_matrix_unitaryGroup_invariant
    {n : Type*} [Fintype n] [DecidableEq n]
    {ρ : Matrix n n ℂ} {U : Matrix.unitaryGroup n ℂ}
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ((U : Matrix n n ℂ) * ρ * (U : Matrix n n ℂ)ᴴ).PosSemidef ∧
      ((U : Matrix n n ℂ) * ρ * (U : Matrix n n ℂ)ᴴ).trace = 1 :=
  density_matrix_unitary_invariant hρ htr (Matrix.UnitaryGroup.star_mul_self U)

end QC


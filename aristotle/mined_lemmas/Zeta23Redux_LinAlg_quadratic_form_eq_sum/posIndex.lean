/-
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix

/-- The positive index of a Hermitian matrix: the number of its strictly positive eigenvalues
(counted with multiplicity, i.e. as a number of indices).  For matrices that are not Hermitian
the value is set to `0`. -/

noncomputable def posIndex {d : ℕ} (A : Matrix (Fin d) (Fin d) ℂ) : ℕ :=
  if hA : A.IsHermitian then Nat.card {i : Fin d // 0 < hA.eigenvalues i} else 0

/-- Diagonalisation of the Hermitian form: in the coordinates given by the eigenvector unitary,
`x ↦ Re (star x ⬝ᵥ A *ᵥ x)` becomes `∑ i, eigenvalue i * ‖coordinate i‖²`. -/

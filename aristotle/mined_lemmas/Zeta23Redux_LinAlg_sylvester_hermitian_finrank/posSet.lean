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

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The (finite) set of indices at which a Hermitian matrix has a strictly positive
eigenvalue. -/

noncomputable def posSet (hA : A.IsHermitian) : Finset (Fin d) :=
  Finset.univ.filter fun i => 0 < hA.eigenvalues i

/-- The positive index of inertia of a Hermitian matrix: the number of its strictly positive
eigenvalues (counted with multiplicity). -/

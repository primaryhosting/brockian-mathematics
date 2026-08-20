/-
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Statement: Every mixed state has a purification, unique up to isometry on the ancilla.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

A mixed state on `ℂ^n` is modelled by a density matrix `rho : Matrix n n ℂ`, i.e. a positive
semidefinite matrix of unit trace.  A vector of the composite system `ℂ^n ⊗ ℂ^m` is modelled by
a matrix `M : Matrix n m ℂ` (its matrix of coefficients in the product basis), the squared
Hilbert–Schmidt norm `∑ i j, ‖M i j‖ ^ 2` being its squared norm as a vector, and its partial
trace over the ancilla `ℂ^m` being `M * Mᴴ`.

The main result `QI.purification_exists` states that every mixed state `rho` has a purification
by a unit vector of `ℂ^n ⊗ ℂ^n`, and that any two purifications with the same ancilla differ by
a unitary acting on the ancilla only.
-/

open scoped BigOperators
open scoped ComplexConjugate
open scoped ComplexOrder
open scoped MatrixOrder

namespace QI

open Matrix

/-- A *mixed state* (density matrix) on the finite-dimensional Hilbert space `ℂ^n`:
a positive semidefinite matrix of unit trace. -/

def IsPurification {n m : Type*} [Fintype n] [Fintype m]
    (rho : Matrix n n ℂ) (M : Matrix n m ℂ) : Prop :=
  M * Mᴴ = rho

section Aux

variable {n m : Type*} [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

omit [DecidableEq m] in
/-- The inner products between the images of the map `x ↦ Mᴴ x` are determined by `M * Mᴴ`. -/

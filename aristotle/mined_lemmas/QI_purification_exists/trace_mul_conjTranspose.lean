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

lemma trace_mul_conjTranspose (M : Matrix n m ℂ) :
    (M * Mᴴ).trace = ((∑ i, ∑ j, ‖M i j‖ ^ 2 : ℝ) : ℂ) := by
  push_cast
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_conj, Complex.normSq_eq_norm_sq]

end Aux

/-- **Purification of mixed states.**

For every mixed state `rho` on `ℂ^n` (a positive semidefinite matrix of unit trace):

* **Existence**: there is a purification `M` of `rho` with ancilla space `ℂ^n`, i.e. a vector
  `M` of `ℂ^n ⊗ ℂ^n` which is a unit vector (`∑ i j, ‖M i j‖ ^ 2 = 1`) and whose partial trace
  over the ancilla, `M * Mᴴ`, is `rho`.
* **Uniqueness up to an isometry on the ancilla**: any two purifications `M`, `N` of `rho`
  with the same ancilla index type `m` differ by a unitary `W` acting on the ancilla alone:
  `N = M * W`. -/

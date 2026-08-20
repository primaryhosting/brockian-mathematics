/-
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Every mixed state has a purification, unique up to a unitary on the ancilla.

A mixed state on an `n`-dimensional Hilbert space `H` is a positive semidefinite matrix `ρ`
of trace one.  A pure state of the composite system `H ⊗ K`, with `K` an `m`-dimensional
ancilla, is encoded by its matrix of coefficients `psi : Matrix (Fin n) (Fin m) ℂ` in the
product basis, and the partial trace over the ancilla is `reducedDensity psi = psi * psiᴴ`.

The uniqueness statement is the operator fact `A Aᴴ = B Bᴴ → ∃ U unitary, B = A U`, which we
derive from `LinearIsometry.extend`: the assignment `Aᴴ x ↦ Bᴴ x` is a well-defined isometry
on `range Aᴴ` and extends to an isometry of the whole space.
-/

open Matrix

open scoped ComplexOrder MatrixOrder

namespace QI

noncomputable section

/-- The reduced density matrix (partial trace over the ancilla) of the pure state `|ψ⟩⟨ψ|`,
where the vector `ψ` of the composite system `H ⊗ K` (`H` of dimension `n`, ancilla `K` of
dimension `m`) is encoded by its coefficient matrix `psi` in the product basis,
`ψ = ∑ i, ∑ j, psi i j • (e i ⊗ f j)`. -/

lemma sum_normSq_eq_trace {n m : ℕ} (psi : Matrix (Fin n) (Fin m) ℂ) :
    ((∑ i, ∑ j, ‖psi i j‖ ^ 2 : ℝ) : ℂ) = (psi * psiᴴ).trace := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_conj']

/-- **Purification exists and is unique up to a unitary on the ancilla.**

For every mixed state `ρ` on an `n`-dimensional Hilbert space (a positive semidefinite matrix
of trace one) there is a unit vector `psi` of the doubled system `H ⊗ K` (`K` a copy of `H`)
whose partial trace over the ancilla `K` is `ρ`; and any two such purifications differ by a
unitary acting on the ancilla only. -/

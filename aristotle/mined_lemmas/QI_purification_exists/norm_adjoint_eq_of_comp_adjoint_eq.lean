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

lemma norm_adjoint_eq_of_comp_adjoint_eq {a b : E →ₗ[ℂ] E}
    (h : a ∘ₗ LinearMap.adjoint a = b ∘ₗ LinearMap.adjoint b) (x : E) :
    ‖LinearMap.adjoint a x‖ = ‖LinearMap.adjoint b x‖ := by
  have key : ∀ c : E →ₗ[ℂ] E, (‖LinearMap.adjoint c x‖ : ℝ) ^ 2
      = RCLike.re (inner ℂ x ((c ∘ₗ LinearMap.adjoint c) x)) := by
    intro c
    have h1 : inner ℂ (LinearMap.adjoint c x) (LinearMap.adjoint c x)
        = inner ℂ x (c (LinearMap.adjoint c x)) := LinearMap.adjoint_inner_left _ _ _
    have h2 := @inner_self_eq_norm_sq ℂ E _ _ _ (LinearMap.adjoint c x)
    simp only [LinearMap.comp_apply]
    rw [← h1, ← h2]
  have ha := key a
  rw [h] at ha
  have hsq : ‖LinearMap.adjoint a x‖ ^ 2 = ‖LinearMap.adjoint b x‖ ^ 2 := by rw [ha, key b]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

/-- Two operators with the same "square" `a a* = b b*` have adjoints related by a linear
isometry of the whole space: there is an isometry `W` with `W (a* x) = b* x`. -/

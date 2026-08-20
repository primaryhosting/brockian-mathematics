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

lemma exists_isometry_of_comp_adjoint_eq {a b : E →ₗ[ℂ] E}
    (h : a ∘ₗ LinearMap.adjoint a = b ∘ₗ LinearMap.adjoint b) :
    ∃ W : E →ₗᵢ[ℂ] E, ∀ x, W (LinearMap.adjoint a x) = LinearMap.adjoint b x := by
  set A' := LinearMap.adjoint a with hA'
  set B' := LinearMap.adjoint b with hB'
  have hnorm : ∀ x, ‖A' x‖ = ‖B' x‖ := norm_adjoint_eq_of_comp_adjoint_eq h
  have hker : LinearMap.ker A' ≤ LinearMap.ker B' := by
    intro x hx
    have hx0 : ‖B' x‖ = 0 := by rw [← hnorm x, LinearMap.mem_ker.mp hx, norm_zero]
    simpa using norm_eq_zero.mp hx0
  -- `B'` factors through `E ⧸ ker A' ≃ range A'`, giving the isometry on `range A'`
  let f : (E ⧸ LinearMap.ker A') →ₗ[ℂ] E := (LinearMap.ker A').liftQ B' hker
  let e := A'.quotKerEquivRange
  let Lm : (LinearMap.range A') →ₗ[ℂ] E := f ∘ₗ (e.symm : LinearMap.range A' →ₗ[ℂ] _)
  have hLm : ∀ x : E, Lm ⟨A' x, LinearMap.mem_range_self _ x⟩ = B' x := by
    intro x
    have he : e (Submodule.Quotient.mk x) = ⟨A' x, LinearMap.mem_range_self _ x⟩ :=
      Subtype.ext (LinearMap.quotKerEquivRange_apply_mk A' x)
    have hs : (e.symm ⟨A' x, LinearMap.mem_range_self _ x⟩) = Submodule.Quotient.mk x := by
      rw [← he, LinearEquiv.symm_apply_apply]
    simp [Lm, hs, f, Submodule.liftQ_apply]
  have hnm : ∀ y : (LinearMap.range A'), ‖Lm y‖ = ‖y‖ := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    rw [hLm x]
    simpa using (hnorm x).symm
  let L : (LinearMap.range A') →ₗᵢ[ℂ] E := ⟨Lm, hnm⟩
  refine ⟨L.extend, fun x => ?_⟩
  have hext := L.extend_apply ⟨A' x, LinearMap.mem_range_self _ x⟩
  simpa [L, hLm x] using hext

/-- A linear isometry of a finite-dimensional space satisfies `W* ∘ W = id`. -/

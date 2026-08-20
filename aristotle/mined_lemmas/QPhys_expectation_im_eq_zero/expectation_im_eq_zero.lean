import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
The variational principle of quantum mechanics: for a self-adjoint Hamiltonian `H` on a
finite-dimensional complex Hilbert space and any nonzero state `ψ`, the Rayleigh quotient
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is bounded below by the ground-state energy `E₀`, i.e. by any real number
that is a lower bound for the spectrum of `H`.

The proof expands `ψ` in the orthonormal eigenbasis supplied by Mathlib's finite-dimensional
spectral theorem (`LinearMap.IsSymmetric.eigenvectorBasis`,
`LinearMap.IsSymmetric.eigenvalues`, `LinearMap.IsSymmetric.apply_eigenvectorBasis`) and uses
Parseval's identity (`OrthonormalBasis.sum_inner_mul_inner`,
`OrthonormalBasis.sum_sq_norm_inner_right`).
-/

open Finset

namespace QPhys

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]

omit [FiniteDimensional ℂ E] in
/-- The expectation value `⟨ψ|H|ψ⟩` of a self-adjoint Hamiltonian is real, so taking its real
part in the statements below loses no information. -/

theorem expectation_im_eq_zero {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) (ψ : E) :
    (inner ℂ ψ (H ψ)).im = 0 := by
  have h : starRingEnd ℂ (inner ℂ ψ (H ψ)) = inner ℂ ψ (H ψ) := by
    rw [inner_conj_symm, hH ψ ψ]
  exact Complex.conj_eq_iff_im.mp h

/-- Expansion of the expectation value `⟨ψ|H|ψ⟩` in an orthonormal eigenbasis of the
symmetric (self-adjoint) operator `H`: it is `∑ᵢ Eᵢ |⟨eᵢ|ψ⟩|²`. -/

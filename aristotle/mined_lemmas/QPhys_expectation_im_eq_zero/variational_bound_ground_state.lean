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

theorem variational_bound_ground_state {m : ℕ} {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric)
    (hn : Module.finrank ℂ E = m + 1) {ψ : E} (hψ : ψ ≠ 0) :
    Module.End.HasEigenvalue H ((hH.eigenvalues hn (Fin.last m) : ℝ) : ℂ) ∧
      hH.eigenvalues hn (Fin.last m) ≤ (inner ℂ ψ (H ψ)).re / (inner ℂ ψ ψ).re := by
  refine ⟨hH.hasEigenvalue_eigenvalues hn (Fin.last m),
    variational_bound hH hn (fun i => ?_) hψ⟩
  exact hH.eigenvalues_antitone hn (Fin.le_last i)

end QPhys


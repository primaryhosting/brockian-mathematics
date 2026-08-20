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

theorem expectation_eq_sum {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric)
    (hn : Module.finrank ℂ E = n) (ψ : E) :
    (inner ℂ ψ (H ψ)).re =
      ∑ i, hH.eigenvalues hn i * ‖inner ℂ (hH.eigenvectorBasis hn i) ψ‖ ^ 2 := by
  have key : ∀ i, inner ℂ ψ (hH.eigenvectorBasis hn i) *
      inner ℂ (hH.eigenvectorBasis hn i) (H ψ)
      = ((hH.eigenvalues hn i * ‖inner ℂ (hH.eigenvectorBasis hn i) ψ‖ ^ 2 : ℝ) : ℂ) := by
    intro i
    have h1 : inner ℂ (hH.eigenvectorBasis hn i) (H ψ)
        = (hH.eigenvalues hn i : ℂ) * inner ℂ (hH.eigenvectorBasis hn i) ψ := by
      rw [← hH (hH.eigenvectorBasis hn i) ψ, hH.apply_eigenvectorBasis hn i, inner_smul_left,
        RCLike.conj_ofReal]
      rfl
    have h2 : inner ℂ ψ (hH.eigenvectorBasis hn i)
        = starRingEnd ℂ (inner ℂ (hH.eigenvectorBasis hn i) ψ) := by
      rw [inner_conj_symm]
    rw [h1, h2, ← mul_assoc, mul_comm _ ((hH.eigenvalues hn i : ℂ)), mul_assoc,
      RCLike.conj_mul]
    push_cast
    rfl
  rw [← (hH.eigenvectorBasis hn).sum_inner_mul_inner ψ (H ψ)]
  simp_rw [key]
  rw [← Complex.ofReal_sum]
  exact Complex.ofReal_re _

/-- **Variational bound (Rayleigh–Ritz).** If `H` is a self-adjoint Hamiltonian on a
finite-dimensional complex Hilbert space and `E₀` is a lower bound for its eigenvalues
(the ground-state energy), then for every nonzero state `ψ`,
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E₀`. -/

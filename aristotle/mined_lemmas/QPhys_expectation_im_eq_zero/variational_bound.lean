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

theorem variational_bound {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric)
    (hn : Module.finrank ℂ E = n) {E₀ : ℝ} (hE₀ : ∀ i, E₀ ≤ hH.eigenvalues hn i)
    {ψ : E} (hψ : ψ ≠ 0) :
    E₀ ≤ (inner ℂ ψ (H ψ)).re / (inner ℂ ψ ψ).re := by
  have hnorm : (inner ℂ ψ ψ).re = ‖ψ‖ ^ 2 := by
    simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have hpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by positivity
  rw [hnorm, le_div_iff₀ hpos, expectation_eq_sum hH hn ψ]
  calc E₀ * ‖ψ‖ ^ 2
      = ∑ i, E₀ * ‖inner ℂ (hH.eigenvectorBasis hn i) ψ‖ ^ 2 := by
        rw [← Finset.mul_sum, (hH.eigenvectorBasis hn).sum_sq_norm_inner_right ψ]
    _ ≤ ∑ i, hH.eigenvalues hn i * ‖inner ℂ (hH.eigenvectorBasis hn i) ψ‖ ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hE₀ i) (by positivity)

/-- The variational bound with the ground-state energy made explicit: on a nonzero
finite-dimensional space, the smallest eigenvalue `E₀` of `H` (Mathlib lists the eigenvalues in
decreasing order, so this is the last one) is a genuine eigenvalue of `H`, and the Rayleigh
quotient of every nonzero state is at least `E₀`. -/

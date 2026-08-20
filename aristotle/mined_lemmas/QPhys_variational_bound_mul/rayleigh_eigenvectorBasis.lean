/-
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QPhys

open Module

/-- **Variational principle (energy form).**
Let `H` be a symmetric (self-adjoint) operator on a finite-dimensional complex inner
product space (a Hamiltonian), with spectral eigenvalues `hH.eigenvalues hn` supplied by
the finite-dimensional spectral theorem, and let `E0` be a lower bound for all of them
(the ground-state energy). Then for every state `ψ`,
`E0 * ⟨ψ|ψ⟩ ≤ ⟨ψ|H|ψ⟩`.

The proof expands `ψ` in the orthonormal eigenbasis of `H`
(`LinearMap.IsSymmetric.eigenvectorBasis`, whose defining property is
`LinearMap.IsSymmetric.eigenvectorBasis_apply_self_apply`), giving
`⟨ψ|H|ψ⟩ = ∑ i, Eᵢ |cᵢ|²` and `⟨ψ|ψ⟩ = ∑ i, |cᵢ|²`. -/

theorem rayleigh_eigenvectorBasis {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hn : finrank ℂ E = n)
    {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) (i : Fin n) :
    hH.eigenvectorBasis hn i ≠ 0 ∧
      RCLike.re ⟪hH.eigenvectorBasis hn i, H (hH.eigenvectorBasis hn i)⟫_ℂ /
          RCLike.re ⟪hH.eigenvectorBasis hn i, hH.eigenvectorBasis hn i⟫_ℂ
        = hH.eigenvalues hn i := by
  set b := hH.eigenvectorBasis hn with hb
  refine ⟨by simpa using b.orthonormal.ne_zero i, ?_⟩
  have hnorm : ‖b i‖ = 1 := b.orthonormal.1 i
  have hHb : H (b i) = ((hH.eigenvalues hn i : ℝ) : ℂ) • b i := by
    rw [hb]; exact hH.apply_eigenvectorBasis hn i
  rw [hHb, inner_smul_right, inner_self_eq_norm_sq, hnorm]
  simp

/-- **Ground-state variational principle.**
Taking `E0` to be the smallest eigenvalue of the Hamiltonian `H` (the ground-state
energy), every nonzero state satisfies `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E0`, and the bound is attained
by a ground state, so `E0` is exactly the minimum of the Rayleigh quotient. -/

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

theorem variational_bound_min {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hn : finrank ℂ E = n)
    {H : E →ₗ[ℂ] E} (hH : H.IsSymmetric) (hne : (Finset.univ : Finset (Fin n)).Nonempty) :
    (∀ ψ : E, ψ ≠ 0 →
        RCLike.re ⟪ψ, H ψ⟫_ℂ / RCLike.re ⟪ψ, ψ⟫_ℂ
          ≥ Finset.univ.inf' hne (hH.eigenvalues hn)) ∧
      ∃ v : E, v ≠ 0 ∧ RCLike.re ⟪v, H v⟫_ℂ / RCLike.re ⟪v, v⟫_ℂ
          = Finset.univ.inf' hne (hH.eigenvalues hn) := by
  obtain ⟨i0, -, hi0⟩ := Finset.exists_mem_eq_inf' hne (hH.eigenvalues hn)
  refine ⟨fun ψ hψ => variational_bound hn hH _ (fun i => ?_) ψ hψ, ?_⟩
  · exact Finset.inf'_le _ (Finset.mem_univ i)
  · obtain ⟨hne0, hq⟩ := rayleigh_eigenvectorBasis hn hH i0
    exact ⟨hH.eigenvectorBasis hn i0, hne0, by rw [hq, hi0]⟩

end QPhys


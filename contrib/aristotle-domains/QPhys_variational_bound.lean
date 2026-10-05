/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Statement: For Hamiltonian H, ⟨ψ|H|ψ⟩/⟨ψ|ψ⟩ ≥ E_0 (ground-state variational bound).
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace QPhys

open scoped InnerProductSpace

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E] {H : E →ₗ[ℂ] E}

/-- The (real part of the) expectation value `⟪ψ, H ψ⟫` expanded in the eigenbasis of `H`. -/
theorem inner_apply_re_eq_sum (hH : H.IsSymmetric) (hn : Module.finrank ℂ E = n) (ψ : E) :
    (⟪ψ, H ψ⟫_ℂ).re
      = ∑ i, hH.eigenvalues hn i * ‖(hH.eigenvectorBasis hn).repr ψ i‖ ^ 2 := by
  set b := hH.eigenvectorBasis hn with hb
  have h1 : ⟪ψ, H ψ⟫_ℂ = ⟪b.repr ψ, b.repr (H ψ)⟫_ℂ := (b.repr.inner_map_map ψ (H ψ)).symm
  rw [h1, PiLp.inner_apply]
  simp only [hb, hH.eigenvectorBasis_apply_self_apply]
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hz : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [← Complex.normSq_eq_norm_sq]; simp [Complex.normSq_apply]; ring
  rw [RCLike.inner_apply, hz]
  simp [Complex.mul_re]
  ring

omit [FiniteDimensional ℂ E] in
/-- Parseval, restated for an arbitrary orthonormal basis. -/
theorem norm_sq_eq_sum_repr (b : OrthonormalBasis (Fin n) ℂ E) (ψ : E) :
    ‖ψ‖ ^ 2 = ∑ i, ‖b.repr ψ i‖ ^ 2 := by
  rw [← b.repr.norm_map ψ, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-- **Variational principle.**  Let `H` be a self-adjoint operator (Hamiltonian) on a
finite-dimensional complex inner product space `E` of dimension `n > 0`, and let
`E₀ = ⨅ i, hH.eigenvalues hn i` be its ground-state energy (the smallest eigenvalue).
Then for every nonzero state `ψ`, the Rayleigh quotient `⟪ψ, H ψ⟫ / ⟪ψ, ψ⟫` is at least `E₀`. -/
theorem variational_bound [NeZero n] (hH : H.IsSymmetric) (hn : Module.finrank ℂ E = n)
    (ψ : E) (hψ : ψ ≠ 0) :
    (⨅ i, hH.eigenvalues hn i) ≤ (⟪ψ, H ψ⟫_ℂ).re / (⟪ψ, ψ⟫_ℂ).re := by
  have : Nonempty (Fin n) := ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne n)⟩⟩
  set E₀ : ℝ := ⨅ i, hH.eigenvalues hn i
  have hE₀ : ∀ i, E₀ ≤ hH.eigenvalues hn i := fun i =>
    ciInf_le (Finite.bddBelow_range _) i
  have hnorm : (⟪ψ, ψ⟫_ℂ).re = ‖ψ‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    exact RCLike.ofReal_re (K := ℂ) _
  have hpos : (0:ℝ) < ‖ψ‖ ^ 2 := by positivity
  rw [hnorm, le_div_iff₀ hpos, inner_apply_re_eq_sum hH hn,
    norm_sq_eq_sum_repr (hH.eigenvectorBasis hn) ψ, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hE₀ i) (by positivity)

end QPhys

#print axioms QPhys.variational_bound


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


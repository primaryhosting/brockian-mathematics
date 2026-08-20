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

open Module

namespace QPhys

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

omit [FiniteDimensional ℂ V] in
/-- Expansion of the expectation value `⟪ψ, H ψ⟫` in an orthonormal eigenbasis `b` of `H`
with (real) eigenvalues `E`. -/

theorem quadratic_form_lower_bound (H : V →ₗ[ℂ] V) (hH : H.IsSymmetric) (E0 : ℝ)
    (hE0 : ∀ μ : ℝ, End.HasEigenvalue H (μ : ℂ) → E0 ≤ μ) (ψ : V) :
    E0 * ‖ψ‖ ^ 2 ≤ (inner ℂ ψ (H ψ)).re := by
  set n := finrank ℂ V
  set b := hH.eigenvectorBasis (rfl : finrank ℂ V = n)
  set E := hH.eigenvalues (rfl : finrank ℂ V = n)
  have hb : ∀ i, H (b i) = (E i : ℂ) • b i := fun i =>
    hH.apply_eigenvectorBasis (rfl : finrank ℂ V = n) i
  have hEi : ∀ i, E0 ≤ E i := fun i =>
    hE0 (E i) (hH.hasEigenvalue_eigenvalues (rfl : finrank ℂ V = n) i)
  have hexp := inner_eigenbasis_expansion b H E hb ψ
  have hre : (inner ℂ ψ (H ψ)).re = ∑ i, E i * ‖(b.repr ψ).ofLp i‖ ^ 2 := by
    rw [hexp, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : starRingEnd ℂ ((b.repr ψ).ofLp i) * (b.repr ψ).ofLp i
        = ((‖(b.repr ψ).ofLp i‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_comm, Complex.mul_conj]
      norm_cast
      exact Complex.normSq_eq_norm_sq _
    rw [this, ← Complex.ofReal_mul, Complex.ofReal_re]
  rw [hre, norm_sq_eq_sum_repr_sq b ψ, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ =>
    mul_le_mul_of_nonneg_right (hEi i) (by positivity)

/-- **Variational bound.**  For a self-adjoint Hamiltonian `H` on a finite-dimensional complex
inner product space whose eigenvalues are all bounded below by the ground state energy `E₀`,
every nonzero state `ψ` satisfies the Rayleigh–Ritz inequality

`⟪ψ, H ψ⟫ / ⟪ψ, ψ⟫ ≥ E₀`. -/

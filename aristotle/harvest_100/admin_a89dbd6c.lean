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

namespace QPhys

/-- **Variational principle (ground-state bound).**

Let `H` be a Hamiltonian on a complex inner product space `E` which is diagonalized by an
orthonormal basis `b` with real eigenvalues `ev` (`H (b i) = ev i • b i`), and let `E₀` be a
lower bound for the spectrum (`E₀ ≤ ev i` for every `i`).  Then for every nonzero state `ψ`
the Rayleigh quotient satisfies
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E₀`,
where `⟨ψ|H|ψ⟩` is the (real part of the) inner product `⟪ψ, H ψ⟫` and `⟨ψ|ψ⟩ = ‖ψ‖ ^ 2`. -/
theorem variational_bound {n : Type*} [Fintype n] {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] (b : OrthonormalBasis n ℂ E) (H : E →ₗ[ℂ] E)
    (ev : n → ℝ) (hev : ∀ i, H (b i) = (ev i : ℂ) • b i)
    (E₀ : ℝ) (hE₀ : ∀ i, E₀ ≤ ev i) (ψ : E) (hψ : ψ ≠ 0) :
    E₀ ≤ (inner ℂ ψ (H ψ)).re / ‖ψ‖ ^ 2 := by
  set c : n → ℂ := fun i => inner ℂ (b i) ψ with hc
  have hconj : ∀ i, inner ℂ ψ (b i) = starRingEnd ℂ (c i) := by
    intro i; rw [hc]; simp [inner_conj_symm]
  -- Expand `ψ` in the eigenbasis.
  have hexp : ψ = ∑ i, c i • b i := by
    conv_lhs => rw [← b.sum_repr ψ]
    exact Finset.sum_congr rfl fun i _ => by rw [b.repr_apply_apply]
  have hH : H ψ = ∑ i, ((ev i : ℂ) * c i) • b i := by
    conv_lhs => rw [hexp]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hev i, smul_smul, mul_comm]
  -- The two quadratic forms, computed coefficientwise.
  have h1 : inner ℂ ψ (H ψ) = ∑ i, ((ev i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [hH, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, hconj i, mul_assoc, Complex.mul_conj']
    push_cast; ring
  have h2 : (inner ℂ ψ ψ : ℂ) = ∑ i, ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
    have hrw : (inner ℂ ψ ψ : ℂ) = inner ℂ ψ (∑ i, c i • b i) := by rw [← hexp]
    rw [hrw, inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, hconj i, Complex.mul_conj']
    push_cast; ring
  have hre1 : (inner ℂ ψ (H ψ)).re = ∑ i, ev i * ‖c i‖ ^ 2 := by
    rw [h1, Complex.re_sum]; simp only [Complex.ofReal_re]
  have hre2 : ‖ψ‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 := by
    have h3 := congrArg Complex.re h2
    rw [Complex.re_sum] at h3
    simp only [Complex.ofReal_re] at h3
    rw [← h3, ← inner_self_eq_norm_sq (𝕜 := ℂ) ψ]
    rfl
  have hpos : (0 : ℝ) < ‖ψ‖ ^ 2 := by
    have : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
    positivity
  rw [le_div_iff₀ hpos, hre1, hre2, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hE₀ i) (by positivity)

/-- The variational bound with the explicit ground-state energy: the Rayleigh quotient of any
nonzero state is at least the smallest eigenvalue of `H`. -/
theorem variational_bound_min_eigenvalue {n : Type*} [Fintype n] [Nonempty n] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (b : OrthonormalBasis n ℂ E) (H : E →ₗ[ℂ] E)
    (ev : n → ℝ) (hev : ∀ i, H (b i) = (ev i : ℂ) • b i) (ψ : E) (hψ : ψ ≠ 0) :
    Finset.univ.inf' Finset.univ_nonempty ev ≤ (inner ℂ ψ (H ψ)).re / ‖ψ‖ ^ 2 :=
  variational_bound b H ev hev _ (fun i => Finset.inf'_le ev (Finset.mem_univ i)) ψ hψ

end QPhys


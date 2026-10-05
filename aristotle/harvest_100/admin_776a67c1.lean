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

namespace QPhys

open Finset

variable {n : ℕ} {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Expansion of an inner product against a vector written in an orthonormal basis. -/
lemma inner_orthonormalBasis_combination (b : OrthonormalBasis (Fin n) ℂ V)
    (psi : V) (g : Fin n → ℂ) :
    inner ℂ psi (∑ i, g i • b i) = ∑ i, g i * (starRingEnd ℂ) (inner ℂ (b i) psi) := by
  rw [inner_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_right, ← inner_conj_symm]

/-- The state written in the eigenbasis, with `H` applied. -/
lemma apply_eq_sum (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V) (E : Fin n → ℝ)
    (hH : ∀ i, H (b i) = (E i : ℂ) • b i) (psi : V) :
    H psi = ∑ i, ((E i : ℂ) * inner ℂ (b i) psi) • b i := by
  conv_lhs => rw [← b.sum_repr psi]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LinearMap.map_smul, hH i, smul_smul, b.repr_apply_apply, mul_comm]

/-- **Variational principle.** If `H` is a linear operator on a finite-dimensional complex
inner product space admitting an orthonormal eigenbasis `b` with (real) eigenvalues `E i`,
and `E₀` is a lower bound for all the eigenvalues (e.g. the ground-state energy), then for
every nonzero state `psi` the Rayleigh quotient `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E₀`. -/
theorem variational_bound (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V)
    (E : Fin n → ℝ) (E₀ : ℝ) (hH : ∀ i, H (b i) = (E i : ℂ) • b i)
    (hE₀ : ∀ i, E₀ ≤ E i) (psi : V) (hpsi : psi ≠ 0) :
    E₀ ≤ (inner ℂ psi (H psi)).re / (inner ℂ psi psi).re := by
  set c : Fin n → ℂ := fun i => inner ℂ (b i) psi with hc
  have hconj : ∀ z : ℂ, z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    intro z
    rw [Complex.mul_conj]
    norm_cast
    exact Complex.normSq_eq_norm_sq z
  have hsum : ∑ i, c i • b i = psi := by
    conv_rhs => rw [← b.sum_repr psi]
    exact Finset.sum_congr rfl fun i _ => by rw [hc, b.repr_apply_apply]
  have hnum : (inner ℂ psi (H psi)).re = ∑ i, E i * ‖c i‖ ^ 2 := by
    rw [apply_eq_sum b H E hH psi, inner_orthonormalBasis_combination b psi]
    rw [Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have : (E i : ℂ) * c i * (starRingEnd ℂ) (c i) = ((E i * ‖c i‖ ^ 2 : ℝ) : ℂ) := by
      rw [mul_assoc, hconj]
      push_cast
      ring
    rw [this, Complex.ofReal_re]
  have hden : (inner ℂ psi psi).re = ∑ i, ‖c i‖ ^ 2 := by
    have h := inner_orthonormalBasis_combination b psi c
    rw [hsum] at h
    rw [h, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hconj, Complex.ofReal_re]
  have hdenpos : 0 < (inner ℂ psi psi).re := by
    have h : (inner ℂ psi psi).re = ‖psi‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) psi
    have hne : ‖psi‖ ≠ 0 := norm_ne_zero_iff.mpr hpsi
    rw [h]
    positivity
  rw [le_div_iff₀ hdenpos, hnum, hden, Finset.mul_sum]
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_right (hE₀ i) (sq_nonneg _)

/-- Sanity check: the hypotheses of `variational_bound` are satisfiable (here `H = id`,
all eigenvalues equal to `1`, and `E₀ = 1`). -/
example (psi : EuclideanSpace ℂ (Fin 2)) (hpsi : psi ≠ 0) :
    (1 : ℝ) ≤ (inner ℂ psi ((LinearMap.id : EuclideanSpace ℂ (Fin 2) →ₗ[ℂ] _) psi)).re /
      (inner ℂ psi psi).re :=
  variational_bound (EuclideanSpace.basisFun (Fin 2) ℂ) LinearMap.id (fun _ => 1) 1
    (fun i => by simp) (fun i => le_rfl) psi hpsi

end QPhys


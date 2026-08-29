/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace QPhys

open ComplexConjugate

variable {ι : Type*} [Fintype ι] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/-- Conjugate times itself is the squared norm, as a complex number. -/
private lemma conj_mul_self (z : ℂ) : conj z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
  rw [mul_comm, Complex.mul_conj]
  norm_cast
  simp [Complex.normSq_eq_norm_sq]

/-- Expansion of `⟪ψ, ψ⟫` in an orthonormal basis. -/
lemma inner_self_eq_sum_sq (b : OrthonormalBasis ι ℂ V) (ψ : V) :
    (inner ℂ ψ ψ : ℂ) = ∑ i, ((‖b.repr ψ i‖ ^ 2 : ℝ) : ℂ) := by
  rw [← b.sum_inner_mul_inner ψ ψ]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← b.repr_apply_apply, ← inner_conj_symm (𝕜 := ℂ) (b i) ψ, ← b.repr_apply_apply,
    conj_mul_self]

/-- Expansion of `⟪ψ, Hψ⟫` in an orthonormal eigenbasis of `H`. -/
lemma inner_apply_eq_sum_eigenvalues (b : OrthonormalBasis ι ℂ V) (Hop : V →ₗ[ℂ] V)
    (ev : ι → ℝ) (hev : ∀ i, Hop (b i) = (ev i : ℂ) • b i) (ψ : V) :
    (inner ℂ ψ (Hop ψ) : ℂ) = ∑ i, (ev i : ℂ) * ((‖b.repr ψ i‖ ^ 2 : ℝ) : ℂ) := by
  have hψsum : ψ = ∑ i, (b.repr ψ i) • b i := (b.sum_repr ψ).symm
  have hHψ : Hop ψ = ∑ i, ((ev i : ℂ) * (b.repr ψ i)) • b i := by
    conv_lhs => rw [hψsum]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hev i, smul_smul, mul_comm]
  have hbi : ∀ i, (inner ℂ (b i) (Hop ψ) : ℂ) = (ev i : ℂ) * (b.repr ψ i) := by
    intro i
    rw [hHψ, inner_sum]
    rw [Finset.sum_eq_single i]
    · simp [b.repr_apply_apply, inner_smul_right]
    · intro j _ hj
      simp [inner_smul_right, b.inner_eq_ite, Ne.symm hj]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [← b.sum_inner_mul_inner ψ (Hop ψ)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hbi i, ← inner_conj_symm (𝕜 := ℂ) (b i) ψ, ← b.repr_apply_apply]
  rw [show conj (b.repr ψ i) * ((ev i : ℂ) * b.repr ψ i)
      = (ev i : ℂ) * (conj (b.repr ψ i) * b.repr ψ i) by ring, conj_mul_self]

/-- **Variational bound (Rayleigh–Ritz).**
If `Hop` is an operator on a finite-dimensional complex inner product space admitting an
orthonormal eigenbasis `b` with real eigenvalues `ev i`, all bounded below by the ground-state
energy `E0`, then for every nonzero state `ψ` the Rayleigh quotient
`⟪ψ, Hop ψ⟫ / ⟪ψ, ψ⟫` is at least `E0`. -/
theorem variational_bound (b : OrthonormalBasis ι ℂ V) (Hop : V →ₗ[ℂ] V) (ev : ι → ℝ) (E0 : ℝ)
    (hev : ∀ i, Hop (b i) = (ev i : ℂ) • b i) (hE0 : ∀ i, E0 ≤ ev i)
    (ψ : V) (hψ : ψ ≠ 0) :
    E0 ≤ (inner ℂ ψ (Hop ψ) : ℂ).re / (inner ℂ ψ ψ : ℂ).re := by
  have hnum : (inner ℂ ψ (Hop ψ) : ℂ).re = ∑ i, ev i * ‖b.repr ψ i‖ ^ 2 := by
    rw [inner_apply_eq_sum_eigenvalues b Hop ev hev ψ, Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp
  have hden : (inner ℂ ψ ψ : ℂ).re = ∑ i, ‖b.repr ψ i‖ ^ 2 := by
    rw [inner_self_eq_sum_sq b ψ, Complex.re_sum]
    simp
  have hpos : 0 < (inner ℂ ψ ψ : ℂ).re := by
    have := @inner_self_eq_norm_sq ℂ V _ _ _ ψ
    rw [this]
    have : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
    positivity
  rw [le_div_iff₀ hpos, hnum, hden, Finset.sum_mul]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hE0 i) (by positivity)

end QPhys


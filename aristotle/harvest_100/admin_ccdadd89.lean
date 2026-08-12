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

/-- **Variational principle** (ground-state variational bound).

Let `H` be a Hamiltonian, i.e. a self-adjoint (symmetric) linear operator on a
finite-dimensional complex inner product space `E`, and let `E0` be a lower bound for the
spectrum of `H` (for instance the ground-state energy, the smallest eigenvalue).  Then for
every nonzero state `ψ` the Rayleigh quotient `⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩` is at least `E0`.

Here `⟨ψ|H|ψ⟩` is `re ⟪ψ, H ψ⟫` (the quantity is real since `H` is self-adjoint) and
`⟨ψ|ψ⟩ = ‖ψ‖ ^ 2`. -/
theorem variational_bound {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [FiniteDimensional ℂ E] (hn : Module.finrank ℂ E = n)
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (E0 : ℝ)
    (hE0 : ∀ μ : ℝ, Module.End.HasEigenvalue H (μ : ℂ) → E0 ≤ μ)
    (ψ : E) (hψ : ψ ≠ 0) :
    (inner ℂ ψ (H ψ)).re / ‖ψ‖ ^ 2 ≥ E0 := by
  set b := hH.eigenvectorBasis hn with hb
  have key : ∀ (a : ℂ) (l : ℝ), inner ℂ a ((l : ℂ) * a) = (l : ℂ) * (‖a‖ : ℂ) ^ 2 := by
    intro a l
    have h : (starRingEnd ℂ) a * a = (‖a‖ : ℂ) ^ 2 := Complex.conj_mul' a
    simp only [RCLike.inner_apply]
    linear_combination (l : ℂ) * h
  -- Expand `⟪ψ, H ψ⟫` in an orthonormal eigenbasis of `H`.
  have h1 : (inner ℂ ψ (H ψ) : ℂ) = ∑ i, ((hH.eigenvalues hn i * ‖b.repr ψ i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← b.repr.inner_map_map ψ (H ψ), PiLp.inner_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hb, hH.eigenvectorBasis_apply_self_apply]
    push_cast
    exact key _ _
  have h1' : (inner ℂ ψ (H ψ)).re = ∑ i, hH.eigenvalues hn i * ‖b.repr ψ i‖ ^ 2 := by
    rw [h1, ← Complex.ofReal_sum, Complex.ofReal_re]
  have h2 : ‖ψ‖ ^ 2 = ∑ i, ‖b.repr ψ i‖ ^ 2 := by
    rw [← b.repr.norm_map ψ, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have hpos : 0 < ‖ψ‖ ^ 2 := by positivity
  rw [ge_iff_le, le_div_iff₀ hpos, h1', h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right
    (hE0 (hH.eigenvalues hn i) (hH.hasEigenvalue_eigenvalues hn i)) (by positivity)

/-- The smallest eigenvalue (the ground-state energy) of a self-adjoint operator on a nonzero
finite-dimensional complex inner product space is a lower bound for the whole spectrum. -/
theorem ground_energy_le_of_hasEigenvalue {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hn : Module.finrank ℂ E = m + 1)
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (μ : ℝ)
    (hμ : Module.End.HasEigenvalue H (μ : ℂ)) :
    hH.eigenvalues hn (Fin.last m) ≤ μ := by
  obtain ⟨i, hi⟩ := hH.exists_eigenvalues_eq hn hμ
  have h : hH.eigenvalues hn i = μ := Complex.ofReal_inj.mp hi
  rw [← h]
  exact hH.eigenvalues_antitone hn (Fin.le_last i)

/-- Variational bound with `E0` the ground-state energy, i.e. the smallest eigenvalue of `H`. -/
theorem variational_bound_ground_energy {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hn : Module.finrank ℂ E = m + 1)
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) (ψ : E) (hψ : ψ ≠ 0) :
    (inner ℂ ψ (H ψ)).re / ‖ψ‖ ^ 2 ≥ hH.eigenvalues hn (Fin.last m) :=
  variational_bound hn H hH _ (ground_energy_le_of_hasEigenvalue hn H hH) ψ hψ

/-- The variational bound is sharp: the ground-state energy is attained by an eigenvector. -/
theorem exists_rayleigh_eq_ground_energy {m : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] [FiniteDimensional ℂ E] (hn : Module.finrank ℂ E = m + 1)
    (H : E →ₗ[ℂ] E) (hH : H.IsSymmetric) :
    ∃ ψ : E, ψ ≠ 0 ∧ (inner ℂ ψ (H ψ)).re / ‖ψ‖ ^ 2 = hH.eigenvalues hn (Fin.last m) := by
  set b := hH.eigenvectorBasis hn with hb
  refine ⟨b (Fin.last m), b.toBasis.ne_zero _, ?_⟩
  have hnorm : ‖b (Fin.last m)‖ = 1 := b.norm_eq_one _
  rw [hb, hH.apply_eigenvectorBasis hn (Fin.last m), inner_smul_right]
  simp [hnorm, ← hb, inner_self_eq_norm_sq_to_K]

end QPhys


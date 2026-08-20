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
theorem inner_eigenbasis_expansion {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ V) (H : V →ₗ[ℂ] V)
    (E : Fin n → ℝ) (hb : ∀ i, H (b i) = (E i : ℂ) • b i) (ψ : V) :
    inner ℂ ψ (H ψ)
      = ∑ i, (E i : ℂ) * (starRingEnd ℂ ((b.repr ψ).ofLp i) * (b.repr ψ).ofLp i) := by
  rw [show H ψ = ∑ i, ((E i : ℂ) * (b.repr ψ).ofLp i) • b i from ?_]
  · rw [inner_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [inner_smul_right, ← inner_conj_symm, b.repr_apply_apply]
    ring
  · conv_lhs => rw [← b.sum_repr ψ]
    rw [map_sum]
    simp only [map_smul, hb, smul_smul]
    exact Finset.sum_congr rfl fun i _ => by rw [mul_comm]

omit [FiniteDimensional ℂ V] in
/-- Parseval: the squared norm is the sum of the squared moduli of the coordinates in an
orthonormal basis. -/
theorem norm_sq_eq_sum_repr_sq {n : ℕ} (b : OrthonormalBasis (Fin n) ℂ V) (ψ : V) :
    ‖ψ‖ ^ 2 = ∑ i, ‖(b.repr ψ).ofLp i‖ ^ 2 := by
  rw [← b.repr.norm_map ψ, EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]

/-- **Key intermediate lemma.**  If `H` is a symmetric (self-adjoint) operator whose
eigenvalues are all bounded below by `E₀`, then the quadratic form of `H` satisfies
`E₀ ‖ψ‖² ≤ ⟪ψ, H ψ⟫` for every state `ψ`. -/
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
theorem variational_bound (H : V →ₗ[ℂ] V) (hH : H.IsSymmetric) (E0 : ℝ)
    (hE0 : ∀ μ : ℝ, End.HasEigenvalue H (μ : ℂ) → E0 ≤ μ) (ψ : V) (hψ : ψ ≠ 0) :
    E0 ≤ (inner ℂ ψ (H ψ)).re / (inner ℂ ψ ψ).re := by
  have hnorm : (inner ℂ ψ ψ).re = ‖ψ‖ ^ 2 := by simpa using inner_self_eq_norm_sq (𝕜 := ℂ) ψ
  have hpos : (0:ℝ) < ‖ψ‖ ^ 2 := by
    have : ‖ψ‖ ≠ 0 := norm_ne_zero_iff.mpr hψ
    positivity
  rw [hnorm, le_div_iff₀ hpos]
  exact quadratic_form_lower_bound H hH E0 hE0 ψ

/-- **Existence of the ground state energy.**  On a nontrivial finite-dimensional complex inner
product space, a symmetric Hamiltonian `H` has a least eigenvalue `E₀`, and every nonzero state
`ψ` satisfies the variational bound `⟪ψ, H ψ⟫ / ⟪ψ, ψ⟫ ≥ E₀`. -/
theorem exists_ground_state_energy [Nontrivial V] (H : V →ₗ[ℂ] V) (hH : H.IsSymmetric) :
    ∃ E0 : ℝ, End.HasEigenvalue H (E0 : ℂ) ∧ (∀ μ : ℝ, End.HasEigenvalue H (μ : ℂ) → E0 ≤ μ) ∧
      ∀ ψ : V, ψ ≠ 0 → E0 ≤ (inner ℂ ψ (H ψ)).re / (inner ℂ ψ ψ).re := by
  have hpos : 0 < finrank ℂ V := finrank_pos
  obtain ⟨i0, -, hi0⟩ :=
    Finset.exists_min_image (Finset.univ : Finset (Fin (finrank ℂ V)))
      (hH.eigenvalues (rfl : finrank ℂ V = finrank ℂ V)) ⟨⟨0, hpos⟩, Finset.mem_univ _⟩
  refine ⟨hH.eigenvalues rfl i0, hH.hasEigenvalue_eigenvalues rfl i0, ?_, ?_⟩
  · intro μ hμ
    obtain ⟨i, hi⟩ := hH.exists_eigenvalues_eq (rfl : finrank ℂ V = finrank ℂ V) hμ
    have : hH.eigenvalues rfl i = μ := Complex.ofReal_inj.mp hi
    exact this ▸ hi0 i (Finset.mem_univ i)
  · intro ψ hψ
    refine variational_bound H hH _ (fun μ hμ => ?_) ψ hψ
    obtain ⟨i, hi⟩ := hH.exists_eigenvalues_eq (rfl : finrank ℂ V = finrank ℂ V) hμ
    have : hH.eigenvalues rfl i = μ := Complex.ofReal_inj.mp hi
    exact this ▸ hi0 i (Finset.mem_univ i)

end QPhys


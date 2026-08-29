/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; it is repeated verbatim as the module docstring after the imports.)

import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
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

namespace Phys

/-!
## Setup

We model a quantum system by a complex inner product space `E`.

* The time-reversal operator is an **antiunitary** map `T`, i.e. a conjugate-linear map
  (`T : E →ₗ⋆[ℂ] E`) preserving the inner product up to the conjugation coming from
  `⟪T x, T y⟫ = ⟪y, x⟫`.
* **Half-integer spin** is encoded by the relation `T ∘ T = -1` (for integer spin one has
  `T ∘ T = +1` instead, and then no degeneracy follows).
* **Time-reversal invariance** of the Hamiltonian `A` is the commutation relation `A ∘ T = T ∘ A`.
* Energy levels are real, so an eigenvalue is written `(μ : ℝ)` viewed in `ℂ`.

The conclusion is Kramers' theorem: for every eigenvector `v ≠ 0` of `A` with eigenvalue `μ`,
the vector `T v` is a *further* eigenvector with the same eigenvalue, is nonzero, is orthogonal
to `v`, and `{v, T v}` is linearly independent — so the level `μ` is (at least) doubly degenerate.
-/

/-- **Kramers degeneracy.**  In a time-reversal invariant system with half-integer spin
(`T` antiunitary with `T ∘ T = -1`, commuting with the Hamiltonian `A`), every eigenvector
`v ≠ 0` of `A` with (real) eigenvalue `μ` gives rise to a second, orthogonal eigenvector
`T v` for the same eigenvalue; in particular `v` and `T v` are linearly independent, so the
energy level `μ` is at least doubly degenerate. -/
theorem kramers_degeneracy
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ⋆[ℂ] E) (A : E →ₗ[ℂ] E) (μ : ℝ) (v : E)
    (hTinner : ∀ x y, ⟪T x, T y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hT2 : ∀ x, T (T x) = -x)
    (hcomm : ∀ x, A (T x) = T (A x))
    (hv : v ≠ 0) (hAv : A v = (μ : ℂ) • v) :
    T v ≠ 0 ∧ A (T v) = (μ : ℂ) • T v ∧ ⟪v, T v⟫_ℂ = 0 ∧
      LinearIndependent ℂ ![v, T v] := by
  -- `T v ≠ 0`, since `T (T v) = -v ≠ 0`.
  have hTv : T v ≠ 0 := by
    intro h
    apply hv
    have h2 := hT2 v
    rw [h, map_zero] at h2
    simpa using h2.symm
  -- `T v` is an eigenvector for the same (real) eigenvalue.
  have heig : A (T v) = (μ : ℂ) • T v := by
    rw [hcomm, hAv, map_smulₛₗ]
    simp
  -- Orthogonality: `⟪T v, v⟫ = ⟪T v, T (T v)⟫ * (-1)` forces `⟪T v, v⟫ = 0`.
  have horth : ⟪T v, v⟫_ℂ = 0 := by
    have h1 := hTinner v (T v)
    rw [hT2 v, inner_neg_right] at h1
    linear_combination -h1 / 2
  have horth' : ⟪v, T v⟫_ℂ = 0 := by
    rw [← inner_conj_symm, horth]
    simp
  refine ⟨hTv, heig, horth', ?_⟩
  -- Two nonzero orthogonal vectors are linearly independent.
  rw [LinearIndependent.pair_iff]
  intro s t hst
  refine ⟨?_, ?_⟩
  · have h := congrArg (fun w => ⟪v, w⟫_ℂ) hst
    simp [horth'] at h
    exact h.resolve_right hv
  · have h := congrArg (fun w => ⟪T v, w⟫_ℂ) hst
    simp [horth] at h
    exact h.resolve_right hTv

/-- Dimension form of Kramers' theorem: under the same hypotheses, the eigenspace of the
Hamiltonian for the level `μ` has rank at least `2`. -/
theorem kramers_eigenspace_rank
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    (T : E →ₗ⋆[ℂ] E) (A : E →ₗ[ℂ] E) (μ : ℝ) (v : E)
    (hTinner : ∀ x y, ⟪T x, T y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hT2 : ∀ x, T (T x) = -x)
    (hcomm : ∀ x, A (T x) = T (A x))
    (hv : v ≠ 0) (hAv : A v = (μ : ℂ) • v) :
    2 ≤ Module.rank ℂ (Module.End.eigenspace A (μ : ℂ)) := by
  obtain ⟨-, heig, -, hli⟩ := kramers_degeneracy T A μ v hTinner hT2 hcomm hv hAv
  have hvS : v ∈ Module.End.eigenspace A (μ : ℂ) := Module.End.mem_eigenspace_iff.mpr hAv
  have hTvS : T v ∈ Module.End.eigenspace A (μ : ℂ) := Module.End.mem_eigenspace_iff.mpr heig
  have h : ((2 : ℕ) : Cardinal) ≤ Module.rank ℂ (Module.End.eigenspace A (μ : ℂ)) := by
    rw [Module.le_rank_iff]
    refine ⟨![⟨v, hvS⟩, ⟨T v, hTvS⟩], ?_⟩
    apply LinearIndependent.of_comp (Module.End.eigenspace A (μ : ℂ)).subtype
    convert hli using 1
    ext i
    fin_cases i <;> rfl
  simpa using h

/-- Finite-dimensional form of Kramers' theorem: every energy level of a time-reversal
invariant half-integer-spin system has multiplicity at least `2`. -/
theorem kramers_eigenspace_finrank
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ⋆[ℂ] E) (A : E →ₗ[ℂ] E) (μ : ℝ) (v : E)
    (hTinner : ∀ x y, ⟪T x, T y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hT2 : ∀ x, T (T x) = -x)
    (hcomm : ∀ x, A (T x) = T (A x))
    (hv : v ≠ 0) (hAv : A v = (μ : ℂ) • v) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace A (μ : ℂ)) := by
  have h := kramers_eigenspace_rank T A μ v hTinner hT2 hcomm hv hAv
  rw [← Module.finrank_eq_rank] at h
  exact_mod_cast h

end Phys


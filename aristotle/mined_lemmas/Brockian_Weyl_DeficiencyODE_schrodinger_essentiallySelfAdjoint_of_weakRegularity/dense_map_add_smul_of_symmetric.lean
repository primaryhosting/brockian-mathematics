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
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped InnerProductSpace ComplexConjugate ENNReal
open Filter

namespace Brockian.Weyl.DeficiencyODE

/-!
## Abstract deficiency criterion

An unbounded operator is presented here as a linear map `T` on a complex Hilbert space `H`
together with a distinguished (dense) *domain* `D`; the operator of interest is the
restriction `T|_D`.  Essential self-adjointness of a densely defined symmetric operator is
equivalent to the vanishing of both deficiency spaces `ker (T* ∓ i)`, i.e. to the density of
the ranges of `T ± i`; this is the definition used below.
-/

section Abstract

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- `T` is symmetric on the domain `D`: `⟪T x, y⟫ = ⟪x, T y⟫` for `x, y ∈ D`. -/

theorem dense_map_add_smul_of_symmetric [CompleteSpace H] (T : H →ₗ[ℂ] H)
    (hT : ∀ x y, ⟪T x, y⟫_ℂ = ⟪x, T y⟫_ℂ) (D : Submodule ℂ H) (hD : Dense (D : Set H))
    (z : ℂ) (hz : z.im ≠ 0) :
    Dense ((D.map (T + z • LinearMap.id) : Submodule ℂ H) : Set H) := by
  set A : H →ₗ[ℂ] H := T + z • LinearMap.id with hA
  have horth : (D.map A)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    rw [Submodule.mem_orthogonal] at hy
    -- a vector orthogonal to the range of `T + z` is a deficiency vector: `T y = -conj z • y`
    have key : ∀ x ∈ D, ⟪x, T y + (conj z) • y⟫_ℂ = 0 := by
      intro x hx
      have h0 := hy (A x) ⟨x, hx, rfl⟩
      rw [hA] at h0
      simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.id_apply,
        inner_add_left, inner_smul_left] at h0
      rw [hT x y] at h0
      rw [inner_add_right, inner_smul_right]
      linear_combination h0
    have hu : T y + (conj z) • y = 0 :=
      hD.eq_zero_of_inner_right fun v => key v v.2
    have hTy : T y = -((conj z) • y) := by linear_combination (norm := module) hu
    -- symmetry forces the eigenvalue to be real, which is impossible unless `y = 0`
    have h1 : ⟪y, T y⟫_ℂ = ⟪T y, y⟫_ℂ := (hT y y).symm
    rw [hTy] at h1
    simp only [inner_neg_right, inner_neg_left, inner_smul_right, inner_smul_left,
      RingHomCompTriple.comp_apply, RingHom.id_apply] at h1
    have h2 : (z - conj z) * ⟪y, y⟫_ℂ = 0 := by linear_combination h1
    have h3 : z - conj z ≠ 0 := by
      rw [Complex.sub_conj]
      simp [hz, Complex.ext_iff]
    have h4 : ⟪y, y⟫_ℂ = 0 := by
      rcases mul_eq_zero.mp h2 with h | h
      · exact absurd h h3
      · exact h
    exact inner_self_eq_zero.mp h4
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  exact horth

/-- **Essential self-adjointness criterion.** A symmetric operator that is defined on all of
`H` is essentially self-adjoint on every dense domain. -/

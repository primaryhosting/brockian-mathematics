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

/-!
# Stone's theorem

A strongly continuous one-parameter unitary group `U : ℝ → (H →L[ℂ] H)` on a complex Hilbert
space `H` has a self-adjoint (in general unbounded) generator `A`, characterized by
`d/dt (U t x) |_{t=0} = i • A x`.
-/

namespace QPhys

open scoped InnerProductSpace
open Complex (I)

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space. -/
structure IsUnitaryGroup (U : ℝ → (H →L[ℂ] H)) : Prop where
  /-- Each `U t` is a unitary operator. -/
  mem_unitary : ∀ t, U t ∈ unitary (H →L[ℂ] H)
  /-- The group law. -/
  map_add : ∀ s t : ℝ, U (s + t) = U s * U t
  /-- Strong continuity. -/
  strong_continuous : ∀ x : H, Continuous fun t => U t x

namespace IsUnitaryGroup

variable {U : ℝ → (H →L[ℂ] H)} (hU : IsUnitaryGroup U)
include hU


theorem exists_sub_I_eq (z : H) :
    ∃ x : (generator U).domain, generator U x - I • (x : H) = z := by
  have hGclosed : IsClosed (((generator U).graph : Submodule ℂ (H × H)) : Set (H × H)) :=
    generator_isClosed hU
  haveI : CompleteSpace ↑((generator U).graph) := hGclosed.completeSpace_coe
  set S : (H × H) →L[ℂ] H :=
    (ContinuousLinearMap.snd ℂ H H) - I • (ContinuousLinearMap.fst ℂ H H) with hS
  set phi : ↑((generator U).graph) →L[ℂ] H := S.comp ((generator U).graph).subtypeL with hphi
  have hphi_apply : ∀ p : ↑((generator U).graph),
      phi p = (p : H × H).2 - I • (p : H × H).1 := by
    intro p
    simp [hphi, hS]
  have hgraph_mem : ∀ x : (generator U).domain,
      (((x : H), generator U x) : H × H) ∈ (generator U).graph := by
    intro x
    exact (LinearPMap.mem_graph_iff _).mpr ⟨x, rfl, rfl⟩
  set K : Submodule ℂ H := LinearMap.range (phi : ↑((generator U).graph) →ₗ[ℂ] H) with hK
  have hmemK : ∀ x : (generator U).domain,
      (generator U x - I • (x : H)) ∈ K := by
    intro x
    refine ⟨⟨((x : H), generator U x), hgraph_mem x⟩, ?_⟩
    simpa using hphi_apply ⟨((x : H), generator U x), hgraph_mem x⟩
  -- the range is closed
  have hanti : AntilipschitzWith 1 phi := by
    refine AddMonoidHomClass.antilipschitz_of_bound phi ?_
    intro p
    obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).mp p.2
    have hp1 : (p : H × H).1 = (x : H) := hx1.symm
    have hp2 : (p : H × H).2 = generator U x := hx2.symm
    have hnormsq : ‖phi p‖ ^ 2 = ‖generator U x‖ ^ 2 + ‖(x : H)‖ ^ 2 := by
      rw [hphi_apply p, hp1, hp2]
      exact norm_sub_I_smul_sq hU x
    have hpn : ‖(p : H × H)‖ = max ‖(x : H)‖ ‖generator U x‖ := by
      rw [Prod.norm_def, hp1, hp2]
    have h1 : ‖(p : H × H)‖ ^ 2 ≤ ‖phi p‖ ^ 2 := by
      rw [hpn, hnormsq]
      rcases max_cases ‖(x : H)‖ ‖generator U x‖ with ⟨he, _⟩ | ⟨he, _⟩ <;> rw [he] <;>
        nlinarith [norm_nonneg (x : H), norm_nonneg (generator U x)]
    have h2 : ‖(p : H × H)‖ ≤ ‖phi p‖ := by
      nlinarith [norm_nonneg (p : H × H), norm_nonneg (phi p), h1]
    simpa using h2
  have hclosedrange : IsClosed (Set.range phi) :=
    hanti.isClosed_range phi.uniformContinuous
  have hKclosed : IsClosed (K : Set H) := by
    rw [hK, LinearMap.coe_range]
    exact hclosedrange
  haveI : CompleteSpace ↑K := hKclosed.completeSpace_coe
  haveI : K.HasOrthogonalProjection := Submodule.HasOrthogonalProjection.ofCompleteSpace K
  -- the orthogonal complement is trivial
  have hbot : Kᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have horth : ∀ x : (generator U).domain, ⟪generator U x - I • (x : H), y⟫_ℂ = 0 := by
      intro x
      exact (Submodule.mem_orthogonal K y).mp hy _ (hmemK x)
    have hkey : ∀ x : (generator U).domain, ⟪(-I : ℂ) • y, (x : H)⟫_ℂ = ⟪y, generator U x⟫_ℂ := by
      intro x
      have h0 := horth x
      rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h0
      have h1 : ⟪generator U x, y⟫_ℂ = -I * ⟪(x : H), y⟫_ℂ := by
        simpa [Complex.conj_I] using h0
      have h2 : ⟪y, generator U x⟫_ℂ = (starRingEnd ℂ) (⟪generator U x, y⟫_ℂ) := by
        rw [inner_conj_symm]
      rw [h2, h1, inner_smul_left, map_mul, inner_conj_symm]
    have hydom : y ∈ ((generator U).adjoint).domain :=
      LinearPMap.mem_adjoint_domain_of_exists y ⟨(-I : ℂ) • y, hkey⟩
    have hyval : (generator U).adjoint ⟨y, hydom⟩ = (-I : ℂ) • y :=
      LinearPMap.adjoint_apply_eq (dense_domain hU) ⟨y, hydom⟩ hkey
    exact eq_zero_of_adjoint_eq_smul hU (-I) (Or.inr rfl) ⟨y, hydom⟩ hyval
  have hKtop : K = ⊤ := Submodule.orthogonal_eq_bot_iff.mp hbot
  have hz : z ∈ K := by rw [hKtop]; trivial
  obtain ⟨p, hp⟩ := hz
  obtain ⟨x, hx1, hx2⟩ := (LinearPMap.mem_graph_iff _).mp p.2
  refine ⟨x, ?_⟩
  have := hphi_apply p
  rw [← hx1, ← hx2] at this
  rw [← hp]
  simpa using this.symm

/-- Every element of the domain of the adjoint lies in the domain of the generator. -/

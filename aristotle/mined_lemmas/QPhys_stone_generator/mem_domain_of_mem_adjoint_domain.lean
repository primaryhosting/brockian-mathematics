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


theorem mem_domain_of_mem_adjoint_domain (f : H) (hf : f ∈ ((generator U).adjoint).domain) :
    ∃ h : f ∈ (generator U).domain,
      generator U ⟨f, h⟩ = (generator U).adjoint ⟨f, hf⟩ := by
  have hle := generator_le_adjoint hU
  obtain ⟨ψ, hψ⟩ := exists_sub_I_eq hU ((generator U).adjoint ⟨f, hf⟩ - I • f)
  have hψd : ((ψ : H)) ∈ ((generator U).adjoint).domain := hle.1 ψ.2
  have hAdψ : (generator U).adjoint ⟨(ψ : H), hψd⟩ = generator U ψ := (hle.2 rfl).symm
  have hsub : f - (ψ : H) ∈ ((generator U).adjoint).domain :=
    Submodule.sub_mem _ hf hψd
  have hval : (generator U).adjoint ⟨f - (ψ : H), hsub⟩ = I • (f - (ψ : H)) := by
    have hlin : (generator U).adjoint ⟨f - (ψ : H), hsub⟩
        = (generator U).adjoint ⟨f, hf⟩ - (generator U).adjoint ⟨(ψ : H), hψd⟩ := by
      have := ((generator U).adjoint).map_sub ⟨f, hf⟩ ⟨(ψ : H), hψd⟩
      simpa using this
    rw [hlin, hAdψ]
    have : generator U ψ = ((generator U).adjoint ⟨f, hf⟩ - I • f) + I • (ψ : H) := by
      rw [← hψ]; abel
    rw [this, smul_sub]
    abel
  have hzero : ((⟨f - (ψ : H), hsub⟩ : ((generator U).adjoint).domain) : H) = 0 :=
    eq_zero_of_adjoint_eq_smul hU I (Or.inl rfl) ⟨f - (ψ : H), hsub⟩ hval
  have hfψ : f = (ψ : H) := by
    have h0 : f - (ψ : H) = 0 := hzero
    exact sub_eq_zero.mp h0
  subst hfψ
  refine ⟨ψ.2, ?_⟩
  rw [hAdψ]

/-- **Stone's theorem**: the generator of a strongly continuous one-parameter unitary group is
self-adjoint, i.e. `A† = A`. -/

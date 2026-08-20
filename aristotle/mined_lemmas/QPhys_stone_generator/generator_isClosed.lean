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


theorem generator_isClosed : (generator U).IsClosed := by
  have hseq : IsSeqClosed ((generator U).graph : Set (H × H)) := by
    intro p q hp hpq
    have h1 : Filter.Tendsto (fun n => (p n).1) Filter.atTop (nhds q.1) :=
      (continuous_fst.tendsto q).comp hpq
    have h2 : Filter.Tendsto (fun n => (p n).2) Filter.atTop (nhds q.2) :=
      (continuous_snd.tendsto q).comp hpq
    have key : ∀ t : ℝ, U t q.1 - q.1 = (I : ℂ) • ∫ s in (0:ℝ)..t, U s q.2 := by
      intro t
      have hEq : ∀ n, (I : ℂ) • (∫ s in (0:ℝ)..t, U s ((p n).2)) = U t ((p n).1) - (p n).1 := by
        intro n
        obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff _).mp (hp n)
        have hform := integral_formula hU y t
        rw [hy1, hy2] at hform
        exact hform
      have hL : Filter.Tendsto (fun n => (I : ℂ) • ∫ s in (0:ℝ)..t, U s ((p n).2)) Filter.atTop
          (nhds ((I : ℂ) • ∫ s in (0:ℝ)..t, U s q.2)) :=
        (tendsto_integral_of_tendsto hU t h2).const_smul (I : ℂ)
      have hR : Filter.Tendsto (fun n => U t ((p n).1) - (p n).1) Filter.atTop
          (nhds (U t q.1 - q.1)) :=
        (((U t).continuous.tendsto q.1).comp h1).sub h1
      have hL' : Filter.Tendsto (fun n => U t ((p n).1) - (p n).1) Filter.atTop
          (nhds ((I : ℂ) • ∫ s in (0:ℝ)..t, U s q.2)) := by
        simpa [hEq] using hL
      exact tendsto_nhds_unique hR hL'
    obtain ⟨hx, hAx⟩ := mem_domain_of_integral_eq hU q.1 q.2 key
    exact (LinearPMap.mem_graph_iff _).mpr ⟨⟨q.1, hx⟩, rfl, hAx⟩
  exact hseq.isClosed

/-- The deficiency spaces are trivial. -/

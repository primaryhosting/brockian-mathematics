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

/-!
# Schrodinger Essentially Self Adjoint Of Weak Regularity
Category: Brockian (Literature Discharge)
Target: Brockian.Weyl.DeficiencyODE.schrodinger_essentiallySelfAdjoint_of_weakRegularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian.Weyl.DeficiencyODE

open Filter Topology

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A linear operator `T` with domain the submodule `D` of a complex Hilbert space is
*symmetric* if `⟪T x, y⟫ = ⟪x, T y⟫` for all `x, y` in the domain. -/

theorem dense_range_add_smul [CompleteSpace H] (hreg : WeakRegularity D T) {c : ℂ}
    (hc : c = Complex.I ∨ c = -Complex.I) (y : H) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : D, ‖(T x + c • (x : H)) - y‖ < ε := by
  set S : Submodule ℂ H := LinearMap.range (T + c • D.subtype) with hSdef
  have hmem : ∀ x : D, T x + c • (x : H) ∈ S := by
    intro x
    exact ⟨x, by simp [LinearMap.add_apply, LinearMap.smul_apply]⟩
  have hSperp : Sᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    have hz' : ∀ x : D, ⟪T x + c • (x : H), z⟫ = 0 := fun x => hz _ (hmem x)
    rcases hc with rfl | rfl
    · refine hreg z (Or.inl ?_)
      intro x
      have h0 := hz' x
      rw [inner_add_left, inner_smul_left] at h0
      rw [inner_smul_right]
      simp only [Complex.conj_I] at h0
      linear_combination h0
    · refine hreg z (Or.inr ?_)
      intro x
      have h0 := hz' x
      rw [inner_add_left, inner_smul_left] at h0
      rw [inner_neg_right, inner_smul_right]
      simp only [map_neg, Complex.conj_I, neg_neg] at h0
      linear_combination h0
  have htop : S.topologicalClosure = ⊤ := Submodule.topologicalClosure_eq_top_iff.mpr hSperp
  have hy : y ∈ closure (S : Set H) := by
    have h1 : y ∈ S.topologicalClosure := by rw [htop]; exact Submodule.mem_top
    rwa [← SetLike.mem_coe, Submodule.topologicalClosure_coe] at h1
  rw [Metric.mem_closure_iff] at hy
  obtain ⟨b, hbS, hb⟩ := hy ε hε
  obtain ⟨x, hx⟩ := hbS
  refine ⟨x, ?_⟩
  have hxb : T x + c • (x : H) = b := by
    rw [← hx]; simp [LinearMap.add_apply, LinearMap.smul_apply]
  rw [hxb, ← dist_eq_norm, dist_comm]
  exact hb

/-- With weak regularity, `T̄ + c` is surjective for `c = ± i`. -/

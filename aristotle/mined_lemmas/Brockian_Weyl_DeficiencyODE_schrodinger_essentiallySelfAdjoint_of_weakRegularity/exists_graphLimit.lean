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

theorem exists_graphLimit [CompleteSpace H] (hsym : IsSymmetricOn D T)
    (hreg : WeakRegularity D T) {c : ℂ} (hc : c = Complex.I ∨ c = -Complex.I) (y : H) :
    ∃ p q : H, GraphLimit D T p q ∧ q + c • p = y := by
  have hcre : c.re = 0 := by rcases hc with rfl | rfl <;> simp
  have hcnorm : ‖c‖ = 1 := by rcases hc with rfl | rfl <;> simp
  have hex : ∀ n : ℕ, ∃ z : D, ‖(T z + c • (z : H)) - y‖ < 1 / (n + 1 : ℝ) := by
    intro n
    exact dense_range_add_smul hreg hc y (by positivity)
  choose x hx using hex
  set s : ℕ → H := fun n => T (x n) + c • (x n : H) with hsdef
  have hs : Tendsto s atTop (𝓝 y) := by
    rw [tendsto_iff_norm_sub_tendsto_zero]
    refine squeeze_zero (fun n => norm_nonneg _) (fun n => (hx n).le) ?_
    exact tendsto_one_div_add_atTop_nhds_zero_nat
  have hkey : ∀ n m : ℕ, ‖(x n : H) - (x m : H)‖ ≤ ‖s n - s m‖ ∧
      ‖T (x n) - T (x m)‖ ≤ ‖s n - s m‖ := by
    intro n m
    have hz : s n - s m = T (x n - x m) + c • ((x n - x m : D) : H) := by
      simp only [hsdef, map_sub, Submodule.coe_sub, smul_sub]
      abel
    have hpy := norm_add_smul_sq hsym hcre (x n - x m)
    rw [← hz] at hpy
    rw [norm_smul, hcnorm, one_mul] at hpy
    rw [map_sub] at hpy
    rw [Submodule.coe_sub] at hpy
    constructor
    · nlinarith [norm_nonneg ((x n : H) - (x m : H)), norm_nonneg (s n - s m),
        norm_nonneg (T (x n) - T (x m))]
    · nlinarith [norm_nonneg ((x n : H) - (x m : H)), norm_nonneg (s n - s m),
        norm_nonneg (T (x n) - T (x m))]
  have hsc : CauchySeq s := hs.cauchySeq
  rw [Metric.cauchySeq_iff] at hsc
  have hxc : CauchySeq (fun n => (x n : H)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hsc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1 ⊢
    exact lt_of_le_of_lt (hkey m n).1 h1
  have hTc : CauchySeq (fun n => T (x n)) := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N, hN⟩ := hsc ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    have h1 := hN m hm n hn
    rw [dist_eq_norm] at h1 ⊢
    exact lt_of_le_of_lt (hkey m n).2 h1
  obtain ⟨p, hp⟩ := cauchySeq_tendsto_of_complete hxc
  obtain ⟨q, hq⟩ := cauchySeq_tendsto_of_complete hTc
  refine ⟨p, q, ⟨x, hp, hq⟩, ?_⟩
  have hlim : Tendsto s atTop (𝓝 (q + c • p)) := hq.add (hp.const_smul c)
  exact tendsto_nhds_unique hlim hs

/-- **Basic criterion** (von Neumann): a symmetric operator with trivial deficiency spaces is
essentially self-adjoint. -/

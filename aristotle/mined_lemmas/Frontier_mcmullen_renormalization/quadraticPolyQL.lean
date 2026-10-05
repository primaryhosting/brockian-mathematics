/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-! ## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard, and the central object of McMullen's work on
renormalization) is a holomorphic map `f : U → V` between bounded open subsets of `ℂ`
with `U ⋐ V`, which is a proper degree-two branched covering onto `V`.

We encode "proper degree two branched covering" concretely and checkably:
`f` maps `U` into `V`, `f` is onto `V`, every fibre over `V` has at most two points,
and `f` has a unique critical point in `U`.
-/

/-- A quadratic-like map: a holomorphic degree-two proper map `f : U → V` with
`closure U ⊆ V` and `U` bounded. -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the large domain -/
  V : Set ℂ
  /-- the map -/
  f : ℂ → ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  /-- `U ⋐ V` : the closure of `U` is contained in `V`. -/
  closure_subset : closure U ⊆ V
  bounded_U : Bornology.IsBounded U
  /-- `f` is holomorphic on `U`. -/
  analytic : AnalyticOnNhd ℂ f U
  mapsTo : Set.MapsTo f U V
  /-- `f : U → V` is onto. -/
  surjOn : Set.SurjOn f U V
  /-- every fibre of `f : U → V` has at most two points (degree two). -/
  fiber_le_two : ∀ w ∈ V, {z | z ∈ U ∧ f z = w}.ncard ≤ 2
  /-- `f` has a unique critical point in `U`. -/
  unique_crit : ∃! c : ℂ, c ∈ U ∧ deriv f c = 0

namespace QuadraticLike

variable (Q : QuadraticLike)


noncomputable def quadraticPolyQL (c : ℂ) : QuadraticLike := by
  classical
  set r : ℝ := ‖c‖ with hr
  set R : ℝ := r + 2 with hRdef
  have hr0 : 0 ≤ r := norm_nonneg c
  have hRpos : 0 < R := by simp [hRdef]; linarith
  have hkey : R + r < R ^ 2 := by nlinarith
  refine
    { U := {z : ℂ | ‖z ^ 2 + c‖ < R}
      V := Metric.ball (0 : ℂ) R
      f := fun z => z ^ 2 + c
      isOpen_U := ?_
      isOpen_V := Metric.isOpen_ball
      closure_subset := ?_
      bounded_U := ?_
      analytic := ?_
      mapsTo := ?_
      surjOn := ?_
      fiber_le_two := ?_
      unique_crit := ?_ }
  · exact isOpen_lt (by fun_prop) continuous_const
  · -- closure U ⊆ V
    have hclosed : IsClosed {z : ℂ | ‖z ^ 2 + c‖ ≤ R} :=
      isClosed_le (by fun_prop) continuous_const
    have hsub : closure {z : ℂ | ‖z ^ 2 + c‖ < R} ⊆ {z : ℂ | ‖z ^ 2 + c‖ ≤ R} :=
      closure_minimal (fun z hz => by exact le_of_lt (Set.mem_setOf.mp hz)) hclosed
    intro z hz
    have hz' : ‖z ^ 2 + c‖ ≤ R := hsub hz
    have h1 : ‖z‖ ^ 2 ≤ R + r := by
      have : ‖z ^ 2‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := by
        calc ‖z ^ 2‖ = ‖(z ^ 2 + c) - c‖ := by ring_nf
          _ ≤ ‖z ^ 2 + c‖ + ‖c‖ := norm_sub_le _ _
      simpa [norm_pow] using this.trans (by linarith [hz'] : ‖z ^ 2 + c‖ + ‖c‖ ≤ R + r)
    have h2 : ‖z‖ < R := by nlinarith [norm_nonneg z]
    simpa [Metric.mem_ball, Complex.dist_eq] using h2
  · -- bounded
    have hclosed : {z : ℂ | ‖z ^ 2 + c‖ < R} ⊆ Metric.ball (0 : ℂ) (R + r + 1) := by
      intro z hz
      have h1 : ‖z‖ ^ 2 ≤ R + r := by
        have : ‖z ^ 2‖ ≤ ‖z ^ 2 + c‖ + ‖c‖ := by
          calc ‖z ^ 2‖ = ‖(z ^ 2 + c) - c‖ := by ring_nf
            _ ≤ ‖z ^ 2 + c‖ + ‖c‖ := norm_sub_le _ _
        have hz' : ‖z ^ 2 + c‖ ≤ R := le_of_lt (Set.mem_setOf.mp hz)
        simpa [norm_pow] using this.trans (by linarith : ‖z ^ 2 + c‖ + ‖c‖ ≤ R + r)
      have : ‖z‖ < R + r + 1 := by nlinarith [norm_nonneg z]
      simpa [Metric.mem_ball, Complex.dist_eq] using this
    exact (Metric.isBounded_ball).subset hclosed
  · intro z _
    exact (analyticAt_id.pow 2).add analyticAt_const
  · intro z hz
    simpa [Metric.mem_ball, Complex.dist_eq] using hz
  · -- surjectivity
    intro w hw
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w - c) (n := 2) (by norm_num)
    have hsU : s ∈ {z : ℂ | ‖z ^ 2 + c‖ < R} := by
      have : s ^ 2 + c = w := by rw [hs]; ring
      rw [Set.mem_setOf_eq, this]
      simpa [Metric.mem_ball, Complex.dist_eq] using hw
    refine ⟨s, hsU, ?_⟩
    show s ^ 2 + c = w
    rw [hs]; ring
  · -- fibres have at most two points
    intro w _
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq (w - c) (n := 2) (by norm_num)
    have hsub : {z : ℂ | z ∈ {z : ℂ | ‖z ^ 2 + c‖ < R} ∧ z ^ 2 + c = w} ⊆ {s, -s} := by
      intro z hz
      have hzw : z ^ 2 + c = w := hz.2
      have hz2 : z ^ 2 = s ^ 2 := by rw [hs]; linear_combination hzw
      have hfac : (z - s) * (z + s) = 0 := by linear_combination hz2
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases mul_eq_zero.1 hfac with h | h
      · left; linear_combination h
      · right; linear_combination h
    have hfin : ({s, -s} : Set ℂ).Finite := (Set.finite_singleton _).insert _
    calc {z : ℂ | z ∈ {z : ℂ | ‖z ^ 2 + c‖ < R} ∧ z ^ 2 + c = w}.ncard
        ≤ ({s, -s} : Set ℂ).ncard := Set.ncard_le_ncard hsub hfin
      _ ≤ 2 := by
          refine le_trans (Set.ncard_insert_le _ _) ?_
          simp
  · -- unique critical point
    have hderiv : ∀ z : ℂ, deriv (fun z : ℂ => z ^ 2 + c) z = 2 * z := by
      intro z; simp
    refine ⟨0, ⟨?_, by simp [hderiv]⟩, ?_⟩
    · show ‖(0 : ℂ) ^ 2 + c‖ < R
      have h0 : ‖(0 : ℂ) ^ 2 + c‖ = r := by simp [hr]
      rw [h0, hRdef]; linarith
    · rintro y ⟨-, hy⟩
      rw [hderiv] at hy
      simpa using hy


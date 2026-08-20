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

/-!
## Quadratic-like maps

A *quadratic-like map* (Douady–Hubbard, and the central object of McMullen's work on
renormalization) is a proper holomorphic map of degree two `f : U → V` between topological
discs in `ℂ` with `closure U` a compact subset of `V`.

We encode this as a structure.  The degree-two condition is encoded by:
* surjectivity of `f : U → V` (`surjOn`),
* every fibre over `V` has at most two points (`deg_le_two`),
* there is a unique critical point `crit ∈ U` (`crit_mem`, `deriv_crit`, `crit_unique`).

Properness of `f : U → V` is recorded in the field `proper`.
-/

/-- A quadratic-like map: a proper degree-two holomorphic map `f : U → V` of plane domains
with `closure U` compact and contained in `V`. -/
structure QuadraticLike where
  /-- the small domain -/
  U : Set ℂ
  /-- the big domain -/
  V : Set ℂ
  /-- the map, given as a globally defined function which is holomorphic on `U` -/
  f : ℂ → ℂ
  /-- the (unique) critical point -/
  crit : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isBounded_V : Bornology.IsBounded V
  closure_U_subset_V : closure U ⊆ V
  analytic : AnalyticOnNhd ℂ f U
  mapsTo : Set.MapsTo f U V
  surjOn : V ⊆ f '' U
  proper : ∀ C ⊆ V, IsCompact C → IsCompact (U ∩ f ⁻¹' C)
  crit_mem : crit ∈ U
  deriv_crit : deriv f crit = 0
  crit_unique : ∀ z ∈ U, deriv f z = 0 → z = crit
  deg_le_two : ∀ w ∈ V, (U ∩ f ⁻¹' {w}).ncard ≤ 2

namespace QuadraticLike

variable (F : QuadraticLike)

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit stays
in the small domain `U`. -/

noncomputable def quadraticLike (c : ℂ) (hc : ‖c‖ < 2) : QuadraticLike where
  U := {z : ℂ | ‖z ^ 2 + c‖ < 2}
  V := Metric.ball (0 : ℂ) 2
  f := fun z => z ^ 2 + c
  crit := 0
  isOpen_U := isOpen_lt (by fun_prop) continuous_const
  isOpen_V := Metric.isOpen_ball
  isBounded_V := Metric.isBounded_ball
  closure_U_subset_V := closure_quadratic_domain c hc
  analytic := fun z _ => sq_add_const_analytic c z (Set.mem_univ z)
  mapsTo := by
    intro z hz
    simpa [Metric.mem_ball, dist_zero_right] using hz
  surjOn := by
    intro w hw
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = w - c := IsSepClosed.exists_pow_nat_eq (w - c) 2
    refine ⟨s, ?_, ?_⟩
    · simp only [Set.mem_setOf_eq, hs]
      simpa [Metric.mem_ball, dist_zero_right] using hw
    · simp [hs]
  proper := by
    intro C hCV hC
    have hset : {z : ℂ | ‖z ^ 2 + c‖ < 2} ∩ (fun z : ℂ => z ^ 2 + c) ⁻¹' C
        = closure {z : ℂ | ‖z ^ 2 + c‖ < 2} ∩ (fun z : ℂ => z ^ 2 + c) ⁻¹' C := by
      apply Set.Subset.antisymm
      · exact Set.inter_subset_inter_left _ subset_closure
      · rintro z ⟨hz1, hz2⟩
        refine ⟨?_, hz2⟩
        have := hCV hz2
        simpa [Metric.mem_ball, dist_zero_right] using this
    rw [hset]
    refine Metric.isCompact_of_isClosed_isBounded
      (isClosed_closure.inter (IsClosed.preimage (by fun_prop) hC.isClosed)) ?_
    refine Bornology.IsBounded.subset ?_ Set.inter_subset_left
    exact (Metric.isBounded_ball).subset (closure_quadratic_domain c hc)
  crit_mem := by simpa using hc
  deriv_crit := by simp
  crit_unique := by
    intro z _ hz
    rw [deriv_sq_add_const] at hz
    simpa using hz
  deg_le_two := by
    intro w _
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s ^ 2 = w - c := IsSepClosed.exists_pow_nat_eq (w - c) 2
    have hsub : {z : ℂ | ‖z ^ 2 + c‖ < 2} ∩ (fun z : ℂ => z ^ 2 + c) ⁻¹' {w} ⊆ {s, -s} := by
      rintro z ⟨-, hz⟩
      have hz2 : z ^ 2 = w - c := by
        have : z ^ 2 + c = w := hz
        linear_combination this
      have hfac : (z - s) * (z + s) = 0 := by linear_combination hz2 - hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases mul_eq_zero.mp hfac with h | h
      · left; linear_combination h
      · right; linear_combination h
    calc ({z : ℂ | ‖z ^ 2 + c‖ < 2} ∩ (fun z : ℂ => z ^ 2 + c) ⁻¹' {w}).ncard
        ≤ ({s, -s} : Set ℂ).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 2 := by
          calc ({s, -s} : Set ℂ).ncard ≤ ({-s} : Set ℂ).ncard + 1 := Set.ncard_insert_le _ _
            _ = 2 := by simp


/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
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

open MeasureTheory Metric Set Filter Function
open scoped ENNReal Topology

/-! ## The Yang–Mills energy

A Yang–Mills field on a manifold `X` is modelled here by its curvature `F : X → V`, a field with
values in a normed space `V` (in the geometric situation, `V` is the space of `𝔤`-valued
two-forms).  Its Yang–Mills energy over a region `s` is `∫_s ‖F‖²`. -/

section Energy

variable {X : Type*} [MeasurableSpace X] {V : Type*} [NormedAddCommGroup V]

/-- The Yang–Mills energy `∫_s ‖F‖²` of a curvature field `F` over the region `s`. -/

lemma finset_card_mul_le_of_subset_bubbleSet {mu : Measure X} {F : ℕ → X → V} {eps Etot : ℝ≥0∞}
    (hbdd : ∀ n, energyOn mu (F n) Set.univ ≤ Etot)
    (S : Finset X) (hS : ↑S ⊆ bubbleSet mu F eps) :
    (S.card : ℝ≥0∞) * eps ≤ Etot := by
  classical
  obtain ⟨d, hd, hsep⟩ := exists_pos_separation S
  have key : ∀ᶠ n in atTop, ∀ x ∈ S, eps ≤ energyOn mu (F n) (ball x (d / 2)) := by
    rw [Filter.eventually_all_finset]
    intro x hx
    exact hS hx (d / 2) (by positivity)
  obtain ⟨n, hn⟩ := key.exists
  have hdisj : (↑S : Set X).PairwiseDisjoint (fun x => ball x (d / 2)) := by
    intro x hx y hy hxy
    refine Metric.ball_disjoint_ball ?_
    have := hsep x (by exact_mod_cast hx) y (by exact_mod_cast hy) hxy
    linarith
  calc (S.card : ℝ≥0∞) * eps = ∑ _x ∈ S, eps := by
        simp [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ x ∈ S, energyOn mu (F n) (ball x (d / 2)) := Finset.sum_le_sum hn
    _ = energyOn mu (F n) (⋃ x ∈ S, ball x (d / 2)) :=
        (energyOn_biUnion_finset hdisj (fun b _ => measurableSet_ball)).symm
    _ ≤ energyOn mu (F n) Set.univ := energyOn_mono _ _ (subset_univ _)
    _ ≤ Etot := hbdd n

/-- **Finiteness of the bubbling set.**  A sequence of Yang–Mills fields of uniformly bounded
energy can concentrate at only finitely many points. -/

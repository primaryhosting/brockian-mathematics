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
Covers, costs, and minimum fragments (Park–Pham).
-/
import Mathlib
import RequestProject.KahnKalai.Measure

open Finset
open scoped Classical

namespace Math2

variable {α : Type*} [DecidableEq α]

/-! ## Covers and their costs -/

/-- `G` is a cover of `H`: every member of `H` contains a member of `G`. -/

lemma sum_powerset_union_aux (r s : ℝ) :
    ∀ (X : Finset α) (g : Finset α → ℝ),
      ∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
          (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
          (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * g (W ∪ V)
        = ∑ U ∈ X.powerset,
          (∏ x ∈ X, (if x ∈ U then r + s - r * s else 1 - (r + s - r * s))) * g U := by
  classical
  intro X
  induction X using Finset.induction_on with
  | empty => intro g; simp
  | insert a X ha ih =>
      intro g
      have key : ∀ (c : ℝ) (W : Finset α), W ⊆ X →
          ((∏ x ∈ insert a X, (if x ∈ W then c else 1 - c))
              = (1 - c) * ∏ x ∈ X, (if x ∈ W then c else 1 - c))
            ∧ ((∏ x ∈ insert a X, (if x ∈ insert a W then c else 1 - c))
              = c * ∏ x ∈ X, (if x ∈ W then c else 1 - c)) := by
        intro c W hW
        have haW : a ∉ W := fun h => ha (hW h)
        have hcongr : ∀ x ∈ X, (if x ∈ insert a W then c else 1 - c)
            = (if x ∈ W then c else 1 - c) := by
          intro x hx
          have hxa : x ≠ a := fun h => ha (h ▸ hx)
          simp [Finset.mem_insert, hxa]
        refine ⟨?_, ?_⟩
        · rw [Finset.prod_insert ha]; simp [haW]
        · rw [Finset.prod_insert ha, Finset.prod_congr rfl hcongr]; simp
      have expand : ∀ (h : Finset α → ℝ) (c d : ℝ),
          (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
            (c * ∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
            (d * ∏ x ∈ X, (if x ∈ V then s else 1 - s)) * h (W ∪ V))
          = c * d * ∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
              (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * h (W ∪ V) := by
        intro h c d
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun W _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun V _ => ?_
        ring
      have expand' : ∀ (h : Finset α → ℝ) (c : ℝ),
          (∑ U ∈ X.powerset, (c * ∏ x ∈ X, (if x ∈ U then r + s - r * s
              else 1 - (r + s - r * s))) * h U)
          = c * ∑ U ∈ X.powerset, (∏ x ∈ X, (if x ∈ U then r + s - r * s
              else 1 - (r + s - r * s))) * h U := by
        intro h c
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun U _ => ?_
        ring
      have e1 : (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
            (∏ x ∈ insert a X, (if x ∈ W then r else 1 - r)) *
            (∏ x ∈ insert a X, (if x ∈ V then s else 1 - s)) * g (W ∪ V))
          = (1 - r) * (1 - s) * (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
              (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * g (W ∪ V)) := by
        rw [← expand g (1 - r) (1 - s)]
        refine Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl fun V hV => ?_
        rw [(key r W (Finset.mem_powerset.mp hW)).1, (key s V (Finset.mem_powerset.mp hV)).1]
      have e2 : (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
            (∏ x ∈ insert a X, (if x ∈ W then r else 1 - r)) *
            (∏ x ∈ insert a X, (if x ∈ insert a V then s else 1 - s)) * g (W ∪ insert a V))
          = (1 - r) * s * (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
              (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * g (insert a (W ∪ V))) := by
        rw [← expand (fun U => g (insert a U)) (1 - r) s]
        refine Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl fun V hV => ?_
        rw [(key r W (Finset.mem_powerset.mp hW)).1, (key s V (Finset.mem_powerset.mp hV)).2,
          Finset.union_insert]
      have e3 : (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
            (∏ x ∈ insert a X, (if x ∈ insert a W then r else 1 - r)) *
            (∏ x ∈ insert a X, (if x ∈ V then s else 1 - s)) * g (insert a W ∪ V))
          = r * (1 - s) * (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
              (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * g (insert a (W ∪ V))) := by
        rw [← expand (fun U => g (insert a U)) r (1 - s)]
        refine Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl fun V hV => ?_
        rw [(key r W (Finset.mem_powerset.mp hW)).2, (key s V (Finset.mem_powerset.mp hV)).1,
          Finset.insert_union]
      have e4 : (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
            (∏ x ∈ insert a X, (if x ∈ insert a W then r else 1 - r)) *
            (∏ x ∈ insert a X, (if x ∈ insert a V then s else 1 - s)) *
              g (insert a W ∪ insert a V))
          = r * s * (∑ W ∈ X.powerset, ∑ V ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ W then r else 1 - r)) *
              (∏ x ∈ X, (if x ∈ V then s else 1 - s)) * g (insert a (W ∪ V))) := by
        rw [← expand (fun U => g (insert a U)) r s]
        refine Finset.sum_congr rfl fun W hW => Finset.sum_congr rfl fun V hV => ?_
        rw [(key r W (Finset.mem_powerset.mp hW)).2, (key s V (Finset.mem_powerset.mp hV)).2,
          Finset.insert_union, Finset.union_insert, Finset.insert_idem]
      have e5 : (∑ U ∈ X.powerset, (∏ x ∈ insert a X, (if x ∈ U then r + s - r * s
              else 1 - (r + s - r * s))) * g U)
          = (1 - (r + s - r * s)) * ∑ U ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ U then r + s - r * s else 1 - (r + s - r * s))) * g U := by
        rw [← expand' g (1 - (r + s - r * s))]
        refine Finset.sum_congr rfl fun U hU => ?_
        rw [(key (r + s - r * s) U (Finset.mem_powerset.mp hU)).1]
      have e6 : (∑ U ∈ X.powerset, (∏ x ∈ insert a X, (if x ∈ insert a U then r + s - r * s
              else 1 - (r + s - r * s))) * g (insert a U))
          = (r + s - r * s) * ∑ U ∈ X.powerset,
              (∏ x ∈ X, (if x ∈ U then r + s - r * s else 1 - (r + s - r * s)))
                * g (insert a U) := by
        rw [← expand' (fun U => g (insert a U)) (r + s - r * s)]
        refine Finset.sum_congr rfl fun U hU => ?_
        rw [(key (r + s - r * s) U (Finset.mem_powerset.mp hU)).2]
      simp only [Finset.sum_powerset_insert ha, Finset.sum_add_distrib]
      rw [e1, e2, e3, e4, e5, e6, ih g, ih fun U => g (insert a U)]
      ring

/-- If `W` is `r`-random and `V` is `s`-random, independently, then `W ∪ V` is
`(r + s - r*s)`-random. -/

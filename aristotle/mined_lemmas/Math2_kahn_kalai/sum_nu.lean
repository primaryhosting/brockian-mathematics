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

lemma sum_nu (p : ℝ) : ∑ A : Finset α, nu p A = 1 := by
  classical
  have := Finset.prod_add (fun _ : α => p) (fun _ : α => 1 - p) Finset.univ
  simp only [Finset.prod_const] at this
  have h1 : ∀ A : Finset α, nu p A = p ^ A.card * (1 - p) ^ (Finset.univ \ A).card := by
    intro A
    rw [nu_eq, Finset.card_univ_diff A]
  calc ∑ A : Finset α, nu p A
      = ∑ A ∈ (Finset.univ : Finset α).powerset, p ^ A.card * (1 - p) ^ (Finset.univ \ A).card := by
        rw [Finset.powerset_univ]
        exact Finset.sum_congr rfl fun A _ => h1 A
    _ = (p + (1 - p)) ^ (Finset.univ : Finset α).card := by
        rw [← this]
    _ = 1 := by norm_num

/-- Sum over a family, bounded by the total mass. -/

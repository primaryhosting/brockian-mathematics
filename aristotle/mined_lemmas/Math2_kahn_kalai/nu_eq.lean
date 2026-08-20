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

lemma nu_eq (p : ℝ) (A : Finset α) :
    nu p A = p ^ A.card * (1 - p) ^ (Fintype.card α - A.card) := by
  classical
  rw [nu, Finset.prod_ite]
  have h1 : (Finset.univ.filter (fun x : α => x ∈ A)) = A := by
    ext x; simp
  have h2 : (Finset.univ.filter (fun x : α => x ∉ A)) = Finset.univ \ A := by
    ext x; simp
  rw [h1, h2, Finset.prod_const, Finset.prod_const, Finset.card_univ_diff A]

/-- The total mass is `1`. -/

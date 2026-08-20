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

lemma nu_split {r : ℝ} (hr : 0 < r) {W U : Finset α} (hd : Disjoint W U) :
    nu r W = nu r (W ∪ U) * ((1 - r) / r) ^ U.card := by
  have hcard : (W ∪ U).card = W.card + U.card := Finset.card_union_of_disjoint hd
  have hle : (W ∪ U).card ≤ Fintype.card α := Finset.card_le_univ _
  rw [nu_eq, nu_eq, hcard]
  have h1 : Fintype.card α - W.card = (Fintype.card α - (W.card + U.card)) + U.card := by
    omega
  rw [h1, pow_add, pow_add, div_pow]
  field_simp

/-- Every member of the step cover has size in `(b, l]`. -/

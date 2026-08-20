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

lemma frag_min {H : Finset (Finset α)} {S : Finset α} (hS : S ∈ H) (W : Finset α) :
    ∀ T ∈ cands H S W, (frag H S W).card ≤ T.card := by
  rw [frag, dif_pos (cands_nonempty hS W)]
  exact (Finset.exists_min_image (cands H S W) Finset.card (cands_nonempty hS W)).choose_spec.2

/-- A minimum fragment of `S` is a subset of `S`. -/

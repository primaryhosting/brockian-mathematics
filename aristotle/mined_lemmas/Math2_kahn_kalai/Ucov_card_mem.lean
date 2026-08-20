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

lemma Ucov_card_mem {H : Finset (Finset α)} {l : ℕ} (hH : ∀ S ∈ H, S.card ≤ l) (b : ℕ)
    (W : Finset α) : ∀ U ∈ Ucov H b W, U.card ∈ Finset.Ico (b + 1) (l + 1) := by
  intro U hU
  obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hU
  rw [Finset.mem_filter] at hS
  have h1 : b < (frag H S W).card := hS.2
  have h2 : (frag H S W).card ≤ l :=
    le_trans (Finset.card_le_card (frag_subset hS.1 W)) (hH _ hS.1)
  simp only [Finset.mem_Ico]
  omega

/-- Decomposition of the cost of the step cover by the size of its members. -/

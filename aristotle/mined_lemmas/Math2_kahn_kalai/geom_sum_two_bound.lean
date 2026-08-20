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

lemma geom_sum_two_bound {y : ℝ} (h0 : 0 ≤ y) (h : y ≤ 1 / 2) (b : ℕ) :
    ∑ m ∈ Finset.range b, y ^ m ≤ 2 := by
  have h1 : ∑ m ∈ Finset.range b, y ^ m ≤ ∑ m ∈ Finset.range b, ((1 : ℝ) / 2) ^ m := by
    gcongr with i hi
  exact le_trans h1 (sum_geometric_two_le b)

/-- The arithmetic estimate behind one step of the bound on `Psi`. -/

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

lemma covCost_le_step {q : ℝ} (hq : 0 ≤ q) (H : Finset (Finset α)) (b : ℕ) (W : Finset α) :
    covCost q H ≤ cost q (Ucov H b W) + covCost q (Hnext H b W) := by
  have h : ∀ G : Finset (Finset α), IsCover G (Hnext H b W) →
      covCost q H - cost q (Ucov H b W) ≤ cost q G := by
    intro G hG
    have h1 : covCost q H ≤ cost q (G ∪ Ucov H b W) := covCost_le_cost hq (isCover_step hG)
    have h2 : cost q (G ∪ Ucov H b W) ≤ cost q G + cost q (Ucov H b W) :=
      cost_union_le hq _ _
    linarith
  have := le_covCost (q := q) (H := Hnext H b W) h
  linarith

end Math2

/-
The `p`-biased product measure on subsets of a finite set, as a finite sum.
-/
import Mathlib

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The weight of the set `A` under the `p`-biased product measure on subsets of `α`:
each element is included independently with probability `p`. -/

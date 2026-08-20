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

lemma cost_Ucov_eq {H : Finset (Finset α)} {l : ℕ} (hH : ∀ S ∈ H, S.card ≤ l) (q : ℝ) (b : ℕ)
    (W : Finset α) :
    cost q (Ucov H b W)
      = ∑ m ∈ Finset.Ico (b + 1) (l + 1),
          (((Ucov H b W).filter (fun U => U.card = m)).card : ℝ) * q ^ m := by
  classical
  rw [cost, ← Finset.sum_fiberwise_of_maps_to (Ucov_card_mem hH b W) (fun U => q ^ U.card)]
  refine Finset.sum_congr rfl fun m _ => ?_
  have hcard : ∀ U ∈ (Ucov H b W).filter (fun U => U.card = m), q ^ U.card = q ^ m := by
    intro U hU
    rw [(Finset.mem_filter.mp hU).2]
  refine (Finset.sum_congr rfl hcard).trans ?_
  rw [Finset.sum_const, nsmul_eq_mul]

/-- The "double counting" bound: the pairs `(W, U)` with `U` a minimum fragment of size `m`
carry total weight at most `2 ^ l`. -/

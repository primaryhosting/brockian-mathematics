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

lemma sum_nu_union (r s : ℝ) (g : Finset α → ℝ) :
    ∑ W : Finset α, ∑ V : Finset α, nu r W * nu s V * g (W ∪ V)
      = ∑ U : Finset α, nu (r + s - r * s) U * g U := by
  classical
  have h := sum_powerset_union_aux (α := α) r s Finset.univ g
  simpa [Finset.powerset_univ, nu] using h

end Math2

/-
The iteration of Park–Pham: at each round the bound on the size of the edges is halved.
-/
import Mathlib
import RequestProject.KahnKalai.KeyLemma

open Finset
open scoped Classical

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The number of halving rounds needed to get from `b` down to `0`
(so `rounds b = ⌊log₂ b⌋ + 1` for `b ≥ 1`). -/

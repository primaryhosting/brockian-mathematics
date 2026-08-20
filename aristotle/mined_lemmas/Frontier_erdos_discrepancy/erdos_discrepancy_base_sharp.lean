import Mathlib
import RequestProject.ErdosDiscrepancy
import RequestProject.ErdosDiscrepancyMathlib
import RequestProject.ErdosDiscrepancySpecialCases
import RequestProject.ErdosDiscrepancyMeasure

/-!
# The base case for completely multiplicative sequences

For a completely multiplicative `±1` sequence every homogeneous sum is `f d` times an
ordinary partial sum, so only the sums `S n = f 1 + ⋯ + f n` matter.  Tracking the four
values `f 2, f 3, f 5, f 7` shows that one of `S 4, S 6, S 8, S 10` must exceed `1` in
absolute value: for completely multiplicative sequences the length `10` already forces
discrepancy `2` (as opposed to `12` in general).
-/

namespace Frontier

/-- Unfolding the ordinary partial sums. -/

theorem erdos_discrepancy_base_sharp :
    ∃ g : ℕ → Int, IsPMOne g ∧
      ∀ d n : ℕ, 1 ≤ d → 1 ≤ n → n * d ≤ 11 → (homogSum g d n).natAbs ≤ 1 :=
  ⟨goodSeq, goodSeq_pm_one, goodSeq_discrepancy_le_one⟩

end Frontier

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

import Mathlib
import RequestProject.ErdosDiscrepancy

/-!
# Erdős discrepancy: Mathlib-idiomatic restatement

`RequestProject/ErdosDiscrepancy.lean` is written in pure Lean core (no imports), so it
uses a recursively defined partial sum `Frontier.homogSum` and `Int.natAbs`.  Here we
identify that partial sum with the Mathlib sum `∑ i ∈ Finset.Icc 1 n, f (i * d)` and
restate the proved base case using `|·|`.
-/

namespace Frontier


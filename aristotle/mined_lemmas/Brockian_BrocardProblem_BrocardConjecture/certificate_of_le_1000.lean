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
import Brockian.BrocardProblem

/-!
# Brocard's problem, in Mathlib's vocabulary

`Brockian/BrocardProblem.lean` is import-free (so that the required header
comment can be its first line), and therefore defines factorial itself as
`Brockian.BrocardProblem.fact`.  Here we check that `fact` agrees with Mathlib's
`Nat.factorial` and restate the two main results using `Nat.factorial`.
-/

namespace Brockian.BrocardProblem

open Nat

/-- The self-contained factorial of `Brockian/BrocardProblem.lean` agrees with
Mathlib's `Nat.factorial`. -/

theorem certificate_of_le_1000 {n : Nat} (h8 : 8 ≤ n) (h1000 : n ≤ 1000) :
    HasCertificate n := by
  have h := checkPair_true_of_range h8 h1000
  simp only [checkPair, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range, bne_iff_ne, ne_eq] at h
  obtain ⟨⟨hp, hr⟩, hx⟩ := h
  refine ⟨(wit n).1, hp, fun x hxlt => ?_⟩
  rw [hr]
  exact hx x hxlt

/-! ### Small values -/

/-- Brocard's conjecture for `n ≤ 7`: `0! + 1 = 2`, `1! + 1 = 2`, `2! + 1 = 3`,
`3! + 1 = 7` and `6! + 1 = 721` are not squares, while `4! + 1 = 5 ^ 2`,
`5! + 1 = 11 ^ 2`, `7! + 1 = 71 ^ 2`. -/

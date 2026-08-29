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

theorem brocard_small {n m : Nat} (hn : n ≤ 7) (h : fact n + 1 = m ^ 2) :
    n = 4 ∨ n = 5 ∨ n = 7 := by
  match n, hn with
  | 0, _ =>
    exact absurd h (ne_sq_of_mod_witness (a := fact 0 + 1) (p := 3) (by omega) (by decide) m)
  | 1, _ =>
    exact absurd h (ne_sq_of_mod_witness (a := fact 1 + 1) (p := 3) (by omega) (by decide) m)
  | 2, _ =>
    exact absurd h (ne_sq_of_mod_witness (a := fact 2 + 1) (p := 4) (by omega) (by decide) m)
  | 3, _ =>
    exact absurd h (ne_sq_of_mod_witness (a := fact 3 + 1) (p := 4) (by omega) (by decide) m)
  | 4, _ => exact Or.inl rfl
  | 5, _ => exact Or.inr (Or.inl rfl)
  | 6, _ =>
    exact absurd h (ne_sq_of_mod_witness (a := fact 6 + 1) (p := 11) (by omega) (by decide) m)
  | 7, _ => exact Or.inr (Or.inr rfl)

/-! ### The verified range and the conditional theorem -/

/-- **Unconditional partial result.**  Brocard's conjecture holds for all
`n ≤ 1000`: the only solutions of `n ! + 1 = m ^ 2` with `n ≤ 1000` are
`n = 4, 5, 7`. -/

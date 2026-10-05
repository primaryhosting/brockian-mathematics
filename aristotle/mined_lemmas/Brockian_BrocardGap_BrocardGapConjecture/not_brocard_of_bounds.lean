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
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Brocard Gap Conjecture
Category: Brockian Conjecture
Target: Brockian.BrocardGap.BrocardGapConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.BrocardGap

open Nat

/-- `n` is a *Brocard number* if `n ! + 1` is a perfect square.
The known Brocard numbers are `4`, `5` and `7` (Brown numbers `(4,5)`, `(5,11)`, `(7,71)`). -/

theorem not_brocard_of_bounds (n k : ℕ) (h1 : k ^ 2 < n ! + 1) (h2 : n ! + 1 < (k + 1) ^ 2) :
    ¬ IsBrocard n := by
  rintro ⟨m, hm⟩
  exact not_square_of_between h1 h2 m hm

/-- **Reduction to pronic numbers.** For `n ≥ 2`, `n ! + 1` is a perfect square if and only if
`n !` is four times a product of two consecutive integers (i.e. `n !/4` is a pronic number). -/

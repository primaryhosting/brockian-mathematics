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

set_option grind.warning false

namespace Chem

/-- A primitive 16-th root of unity. -/

lemma succ_ne_pred (i : Fin 16) : (i + 1 : Fin 16) ≠ i - 1 := by
  revert i; decide

/-- Multiplying by the adjacency matrix sums the two neighbouring entries. -/

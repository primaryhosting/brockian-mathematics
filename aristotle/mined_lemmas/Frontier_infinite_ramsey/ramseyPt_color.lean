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

namespace Frontier

variable (c : ℕ → ℕ → Bool)

open Classical in
/-- The colour chosen at a stage of the Ramsey construction: `true` if the set of elements of
`S` above `sInf S` that are joined to `sInf S` in colour `true` is infinite, `false` otherwise. -/

lemma ramseyPt_color {n m : ℕ} (h : n < m) :
    c (ramseyPt c n) (ramseyPt c m) = ramseyColor c (ramseySeq c n) := by
  have hmem : ramseyPt c m ∈ ramseySeq c (n + 1) :=
    ramseySeq_antitone c h (ramseyPt_mem c m)
  exact color_of_mem_ramseyNext c hmem

/-- **Infinite Ramsey theorem for pairs and two colours**: for every 2-colouring `c` of the
(ordered) pairs of natural numbers there is an infinite set `S ⊆ ℕ` and a colour `i` such that
all pairs from `S` receive the colour `i`. -/

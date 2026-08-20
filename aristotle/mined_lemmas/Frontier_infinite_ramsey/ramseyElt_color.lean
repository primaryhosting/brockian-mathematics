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

section Ramsey

variable (c : ℕ → ℕ → Bool)

/-- The elements of `A` strictly above `a` receiving colour `b` (paired with `a`). -/

theorem ramseyElt_color {m n : ℕ} (h : m < n) :
    c (ramseyElt c m) (ramseyElt c n) = ramseyColor c m := by
  have hmem : ramseyElt c n ∈ ramseySet c (m + 1) :=
    ramseySet_subset_of_le c h (ramseyElt_mem c n)
  exact (mem_succ_color c hmem).2

/-- **Infinite Ramsey for pairs, ordered form**: any `2`-colouring `c` of ordered
pairs `i < j` of naturals admits an infinite set on which `c` is constant. -/

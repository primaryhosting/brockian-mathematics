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

theorem mem_succ_color {n : ℕ} {x : ℕ} (hx : x ∈ ramseySet c (n + 1)) :
    ramseyElt c n < x ∧ c (ramseyElt c n) x = ramseyColor c n :=
  ⟨hx.2.1, hx.2.2⟩


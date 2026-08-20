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

namespace CS

open Nat.Partrec Nat.Partrec.Code

/-- The diagonal partial function: on input `n` it halts (returning `0`) exactly when
`H n n = false`, and diverges otherwise. It is partial recursive whenever `H` is computable. -/

theorem diag_dom_iff (H : ℕ → ℕ → Bool) (n : ℕ) : (diag H n).Dom ↔ H n n = false := by
  constructor
  · intro h
    have := Nat.rfind_spec (Part.get_mem h)
    simpa using this
  · intro h
    have : (0 : ℕ) ∈ diag H n := by
      rw [diag, Nat.mem_rfind]
      simp [h]
    exact this.fst

/-- **Undecidability of the halting problem** (by diagonalization).

There is no total computable function `H` which, given (a code for) a program `c` and an
input `x`, decides whether the program `c` halts on input `x`. -/

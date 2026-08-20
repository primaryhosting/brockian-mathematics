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
import RequestProject.Savitch.Enc

/-!
# The Savitch simulator and its correctness

We build, from a nondeterministic machine `M` and a recursion depth `K`, a
deterministic machine `savitchDM M K` which decides, by Savitch's recursive midpoint
search, whether the sink vertex `none` of the configuration graph of `M` is reachable
from the start vertex within `2 ^ K` steps.  If `cV M ≤ 2 ^ K` this is exactly
acceptance by `M`.
-/

namespace CS
namespace Savitch

variable {Sigma : Type}


theorem savitchDM_accepts_iff_accepts (K : ℕ) (hK : cV M ≤ 2 ^ K) :
    (savitchDM M K).Accepts x ↔ M.Accepts x := by
  rw [savitchDM_accepts_iff, accepts_iff_reachable]
  exact reachIn_iff_reflTransGen hK _ _

end Savitch
end CS

import Mathlib

/-!
# A space-bounded machine model

We use the standard "read-only random access input + bounded work memory" model of
space-bounded computation.

A machine has a finite set of internal states `S` (the *work memory*: a machine with
`|S| ≤ 2^s` states is a machine using `s` bits of work space).  The input `x` is
read-only and does *not* count towards the space; the machine can inspect it only one
symbol at a time: the current state `s` determines an address `addr s`, and the
transition may depend on the symbol of the input found at that address (or `none`, if
the address is out of range).

Deterministic machines have a transition *function*, nondeterministic ones a transition
*relation*, and a nondeterministic machine accepts iff some accepting state is
reachable from the start state.

`DSPACE f` / `NSPACE f` are then the classes of languages decided by (families of)
such machines with `2^(c * f n + c)` states on inputs of length `n`.
-/

namespace CS

/-- A nondeterministic space-bounded machine over the input alphabet `Sigma`. -/
structure NMachine (Sigma : Type) where
  /-- The finite set of internal (work-memory) states. -/
  S : Type
  /-- Finiteness of the state set: `Fintype.card S` measures the space used. -/
  fintypeS : Fintype S
  /-- The initial state. -/
  start : S
  /-- The position of the read-only input head, determined by the current state. -/
  addr : S → ℕ
  /-- The accepting states. -/
  acc : S → Prop
  /-- The transition relation: it may depend on the symbol currently scanned. -/
  next : S → Option Sigma → S → Prop

attribute [instance] NMachine.fintypeS

/-- A deterministic space-bounded machine over the input alphabet `Sigma`. -/
structure DMachine (Sigma : Type) where
  /-- The finite set of internal (work-memory) states. -/
  S : Type
  /-- Finiteness of the state set: `Fintype.card S` measures the space used. -/
  fintypeS : Fintype S
  /-- The initial state. -/
  start : S
  /-- The position of the read-only input head, determined by the current state. -/
  addr : S → ℕ
  /-- The accepting states. -/
  acc : S → Prop
  /-- The transition function: it may depend on the symbol currently scanned. -/
  step : S → Option Sigma → S

attribute [instance] DMachine.fintypeS

variable {Sigma : Type}

/-- One nondeterministic step on the input `x`. -/

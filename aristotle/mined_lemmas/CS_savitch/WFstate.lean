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
import RequestProject.Savitch.Reach

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The deterministic simulator

This file defines the deterministic machine used in Savitch's theorem: an explicit
iterative (stack based) implementation of the recursive procedure

```
REACH d u v  =  if d = 0 then (u = v ∨ u → v)
                else ∃ m, REACH (d-1) u m ∧ REACH (d-1) m v
```

together with its encoding into bit strings and the space accounting: a well-formed
state occupies `O((f n)²)` bits, because the stack holds at most `f n + 2` frames of
`O(f n)` bits each.
-/

namespace CS
namespace Savitch

/-- Classical truth value of a proposition. -/

def WFstate (N : NDetMachine) (f : ℕ → ℕ) (x : Word) : SavState → Prop
  | .count k => k ≤ x.length
  | .scan n j => n = x.length ∧ j ≤ (cands (f x.length)).length
  | .main n j st _ =>
      n = x.length ∧ j < (cands (f x.length)).length ∧ WFstack (f x.length) st
  | .done _ => True

end Savitch
end CS

import Mathlib
import RequestProject.Savitch.Encoding

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Space-bounded machines and the classes `DSPACE` / `NSPACE`

A machine has a read-only input `x : Word`, accessed one symbol at a time through an
input head whose position is determined by the current memory, and a *work memory*
which is itself a bit string.  The **space** used by the machine on an input is the
length of its work memory; this is the only resource that is measured.

Both the deterministic and the nondeterministic model are formalised in this way, so
that Savitch's theorem is a statement purely about memory usage.
-/

namespace CS

/-- A language is a set of bit strings. -/
abbrev Language := Word → Prop

/-- A deterministic space-bounded machine: the work memory is a bit string, the input
head position is a function of the memory, and one step reads the input symbol under the
head (`none` if the head is past the end of the input) and updates the memory. -/
structure DetMachine where
  /-- Position of the (read-only) input head, as a function of the work memory. -/
  head : Word → ℕ
  /-- One computation step: new memory from the old memory and the scanned input symbol. -/
  step : Word → Option Bool → Word
  /-- Halting memory configurations. -/
  halt : Word → Bool
  /-- Output bit of a memory configuration. -/
  out : Word → Bool
  /-- Initial memory. -/
  init : Word
  /-- Halting configurations do not change any more. -/
  halt_fix : ∀ w b, halt w = true → step w b = w

namespace DetMachine

/-- The memory configuration after `t` steps on input `x`. -/

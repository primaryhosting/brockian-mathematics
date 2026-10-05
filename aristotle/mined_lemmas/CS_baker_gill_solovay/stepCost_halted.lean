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

/-!
# A relativized model of computation

We formalise oracle computation by a small imperative register language over bit
strings.  Registers hold finite bit strings (`List Bool`), and a program may query
an oracle (an arbitrary set of bit strings, presented as `Str → Bool`).

The cost model is: each elementary instruction costs one unit, except copying and
querying, which cost one unit plus the length of the string that is moved / written
on the query tape.  This is the usual convention for oracle Turing machines: writing
the query string on the oracle tape takes as many steps as the string is long.
-/

set_option autoImplicit false

namespace BGS

/-- Bit strings. -/
abbrev Str := List Bool

/-- An oracle is an arbitrary set of bit strings. -/
abbrev Oracle := Str → Bool

/-- A language is a set of bit strings. -/
abbrev Lang := Set Str

/-- A register store: countably many registers, each holding a bit string. -/
abbrev St := ℕ → Str

/-- Update one register. -/

lemma stepCost_halted {cf : Cfg} (h : Halted cf) : stepCost cf = 0 := by
  obtain ⟨cont, st⟩ := cf
  simp only [Halted] at h
  subst h
  rfl


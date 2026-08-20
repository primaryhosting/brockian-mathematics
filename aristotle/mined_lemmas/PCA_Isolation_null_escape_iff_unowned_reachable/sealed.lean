import Mathlib

/-!
# A verified model of an isolation engine

This file formalises the abstract model underlying an *isolation engine*: a static
analysis that, given a finite object graph, decides whether the isolate can reach
an object that it does not own (an *escape*).

* `PCA.Isolation.Model` is a finite object graph: each object has a finite set of
  outgoing references (`succ`), there is a finite set of entry points (`roots`), and
  a finite set of objects `owned` by the isolate.
* `PCA.Isolation.Reachable` is the *specification*: the reflexive–transitive closure
  of the reference relation, started at the roots.
* `PCA.Isolation.escapes` is the *engine*: a terminating, decidable fixed-point
  computation (iterated frontier expansion, run for `card V + 1` rounds) which
  reports whether some object outside the ownership set is in the computed closure.

The main theorem `PCA.Isolation.null_escape_iff_unowned_reachable` states that the
engine is both sound and complete for its specification: it reports an escape if and
only if some unowned object is genuinely reachable from the roots.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.Isolation

universe u

/-- A finite object graph together with the isolate's roots and ownership set. -/
structure Model (V : Type u) where
  /-- The references emanating from an object. -/
  succ : V → Finset V
  /-- The entry points of the isolate. -/
  roots : Finset V
  /-- The objects owned by the isolate. -/
  owned : Finset V

variable {V : Type u} [DecidableEq V] (M : Model V)

/-- The reference relation of the model: `b` is directly referenced by `a`. -/

def sealed : Model (Fin 4) where
  succ := ![{1}, {0}, {3}, ∅]
  roots := {0}
  owned := {0, 1}

example : escapes leaky = true := by decide

example : ∃ v, Reachable leaky v ∧ v ∉ leaky.owned :=
  (null_escape_iff_unowned_reachable leaky).mp (by decide)

example : escapes sealed = false := by decide

example : ∀ v, Reachable sealed v → v ∈ sealed.owned :=
  (no_escape_iff_all_reachable_owned sealed).mp (by decide)

end Examples

end PCA.Isolation

import Mathlib
import RequestProject.Isolation

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


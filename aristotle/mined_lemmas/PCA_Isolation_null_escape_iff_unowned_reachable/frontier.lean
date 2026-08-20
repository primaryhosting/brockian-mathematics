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

def frontier (n : ℕ) : Finset V := (step M)^[n] M.roots

/-- The engine's computed reachable set: expansion run to its fixed point.
`Fintype.card V + 1` rounds always suffice. -/

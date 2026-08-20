import Mathlib

/-!
# A formal model of an isolation engine's predicate tightening

This file develops a small, self-contained formal model of the *predicate tightening*
performed by an isolation engine (`PCA.Isolation`).

The engine works with *access predicates*, written in a small Boolean formula language
over atomic checks (`PCA.Isolation.Formula`).  A concrete request is modelled as a
valuation `s : ℕ → Bool` of the atomic checks.

The engine additionally knows a finite set of *isolation facts* `K : Facts`, i.e. atomic
checks whose value is fixed by the isolation context (a sandbox domain, a capability set,
a label, ...).  A request is *admissible* for that context when it agrees with all the
facts (`PCA.Isolation.Consistent`).

Given a predicate `f`, the engine produces the *tightened predicate*
`PCA.Isolation.tighten K f`, obtained by conjoining an explicit guard for the isolation
context with the context-directed simplification of `f`.

The main result, `PCA.Isolation.tightened_predicate_refines_original`, states the
soundness *and* completeness of this construction:

  `(tighten K f).eval s = true ↔ (Consistent K s ∧ f.eval s = true)`

so the tightened predicate accepts exactly the admissible requests accepted by the
original predicate: it never accepts more than the original (soundness / refinement) and
never rejects an admissible request the original would accept (completeness).
-/

set_option maxHeartbeats 1000000

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.Isolation

/-- Access predicates of the isolation engine: Boolean combinations of atomic checks,
atomic checks being indexed by natural numbers. -/
inductive Formula : Type
  | tt : Formula
  | ff : Formula
  | atom : ℕ → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  deriving DecidableEq, Repr

/-- Evaluation of an access predicate at a request `s`, which assigns a Boolean value to
each atomic check. -/

theorem tighten_sound (K : Facts) (f : Formula) (s : ℕ → Bool)
    (h : (tighten K f).eval s = true) : f.eval s = true :=
  ((tightened_predicate_refines_original K f s).mp h).2

/-- Isolation: every request accepted by the tightened predicate is admissible for the
isolation context. -/

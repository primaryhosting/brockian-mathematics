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

theorem frontier_stable_of_eq {n : ℕ} (h : frontier M n = frontier M (n + 1)) :
    ∀ m, n ≤ m → frontier M m = frontier M n := by
  intro m hm
  induction m with
  | zero => simp [Nat.le_zero.mp hm]
  | succ k ih =>
    rcases Nat.lt_or_ge n (k + 1) with hlt | hge
    · have hk : n ≤ k := Nat.lt_succ_iff.mp hlt
      rw [frontier_succ, ih hk, ← frontier_succ, ← h]
    · have : n = k + 1 := le_antisymm hm hge
      rw [this]


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

theorem card_frontier_ge_of_strict [Fintype V] {N : ℕ}
    (h : ∀ n ≤ N, frontier M n ≠ frontier M (n + 1)) :
    ∀ n ≤ N + 1, n ≤ (frontier M n).card := by
  intro n
  induction n with
  | zero => intro _; exact Nat.zero_le _
  | succ k ih =>
    intro hk
    have hkN : k ≤ N := by omega
    have hsub : frontier M k ⊆ frontier M (k + 1) := frontier_subset_succ M k
    have hne : frontier M k ≠ frontier M (k + 1) := h k hkN
    have hlt : (frontier M k).card < (frontier M (k + 1)).card :=
      Finset.card_lt_card (lt_of_le_of_ne hsub hne)
    have := ih (by omega)
    omega


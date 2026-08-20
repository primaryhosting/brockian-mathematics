/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.Isolation

universe u

/-- Abstract model of the isolation engine's heap-with-ownership view.

* `edge a b` means the object `a` holds a reference to the object `b`;
* `owned v` means the isolation engine holds an ownership capability for `v`
  (an *unowned* object models a null / foreign / escaped capability);
* `root r` marks the entry points visible to the component under analysis. -/
structure Heap (V : Type u) where
  /-- Reference edges of the heap graph. -/
  edge : V → V → Prop
  /-- Ownership capability predicate. -/
  owned : V → Prop
  /-- Entry points of the component. -/
  root : V → Prop

variable {V : Type u}

/-- Reachability along reference edges (reflexive–transitive closure of `e`). -/
inductive Reach (e : V → V → Prop) : V → V → Prop
  /-- Every object reaches itself. -/
  | refl (a : V) : Reach e a a
  /-- Prefixing a reference edge to a reachability witness. -/
  | head {a b c : V} : e a b → Reach e b c → Reach e a c

/-- Appending a reference edge at the end of a reachability witness. -/

theorem null_escape_iff_unowned_reachable_mathlib
    (edge : V → V → Prop) (owned : V → Prop) (roots : Set V) :
    (∃ (r : V) (l : List V), r ∈ roots ∧ List.IsChain edge (r :: l) ∧
        ¬ owned ((r :: l).getLast (List.cons_ne_nil _ _)))
      ↔ ∃ r ∈ roots, ∃ v, Relation.ReflTransGen edge r v ∧ ¬ owned v := by
  have key := null_escape_iff_unowned_reachable
    (⟨edge, owned, fun r => r ∈ roots⟩ : Heap V)
  simp only [NullEscapes, UnownedReachable] at key
  constructor
  · rintro ⟨r, l, hr, hchain, hun⟩
    obtain ⟨r', v, hr', hreach, hun'⟩ :=
      key.1 ⟨r, l, hr, (isPath_iff_isChain edge r l).2 hchain, by
        rwa [traceTarget_eq_getLast]⟩
    exact ⟨r', hr', v, (reach_iff_reflTransGen edge r' v).1 hreach, hun'⟩
  · rintro ⟨r, hr, v, hreach, hun⟩
    obtain ⟨r', l, hr', hpath, hun'⟩ :=
      key.2 ⟨r, v, hr, (reach_iff_reflTransGen edge r v).2 hreach, hun⟩
    exact ⟨r', l, hr', (isPath_iff_isChain edge r' l).1 hpath, by
      rwa [traceTarget_eq_getLast] at hun'⟩

end PCA.Isolation

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


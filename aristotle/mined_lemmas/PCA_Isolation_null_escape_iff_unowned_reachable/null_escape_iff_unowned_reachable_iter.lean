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

/-!
# Null Escape Iff Unowned Reachable
Category: Proof-Carrying Apps
Target: PCA.Isolation.null_escape_iff_unowned_reachable
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

universe u

namespace PCA.Isolation

/-- A model of an isolation boundary inside a proof-carrying application.

* `ref a b` holds when object `a` stores a reference to object `b`;
* `roots v` holds when object `v` is directly exposed at the isolation boundary
  (i.e. it can be named from outside the isolate);
* `owned v` holds when object `v` is owned by the isolate.
-/
structure Model (V : Type u) where
  /-- `ref a b` holds when object `a` stores a reference to object `b`. -/
  ref : V → V → Prop
  /-- Objects directly exposed at the isolation boundary. -/
  roots : V → Prop
  /-- Objects owned by the isolate. -/
  owned : V → Prop

variable {V : Type u} (M : Model V)

/-- The escape set computed by the isolation engine, presented as the least
fixpoint of its transfer function: roots escape, and anything referenced from an
escaping object escapes. -/
inductive Escapes (M : Model V) : V → Prop
  | root {v : V} : M.roots v → Escapes M v
  | ref {u v : V} : Escapes M u → M.ref u v → Escapes M v

/-- Concrete semantics: `Reach M a b` holds when `b` can be obtained from `a` by
following a finite chain of references. -/
inductive Reach (M : Model V) : V → V → Prop
  | refl {a : V} : Reach M a a
  | tail {a b c : V} : Reach M a b → M.ref b c → Reach M a c

/-- An object is *reachable* when it can be obtained by following references from
an object exposed at the isolation boundary. -/

theorem null_escape_iff_unowned_reachable_iter :
    (∃ n v, approx M n v ∧ ¬ M.owned v) ↔ UnownedReachable M := by
  constructor
  · intro h
    cases h with
    | intro n hn =>
        cases hn with
        | intro v hv =>
            exact (null_escape_iff_unowned_reachable M).mp ⟨v, escapes_of_approx M hv.1, hv.2⟩
  · intro h
    have h' := (null_escape_iff_unowned_reachable M).mpr h
    cases h' with
    | intro v hv =>
        cases exists_approx_of_escapes M hv.1 with
        | intro n hn => exact ⟨n, v, hn, hv.2⟩

end PCA.Isolation


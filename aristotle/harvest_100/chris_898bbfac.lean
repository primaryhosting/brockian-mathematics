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
def Reaches (v : V) : Prop := ∃ r, M.roots r ∧ Reach M r v

/-- The engine reports a *null escape*: some object in its computed escape set is
not owned by the isolate, so a dereference through the boundary must be nulled
out rather than served. -/
def NullEscape : Prop := ∃ v, Escapes M v ∧ ¬ M.owned v

/-- The semantic defect the engine is meant to detect: some object reachable from
the isolation boundary is not owned by the isolate. -/
def UnownedReachable : Prop := ∃ v, Reaches M v ∧ ¬ M.owned v

/-! ### The engine's escape set is exactly the reachable set -/

/-- Completeness of the engine's escape set: everything reachable from a root is
flagged as escaping. -/
theorem escapes_of_reach {r v : V} (hr : M.roots r) (h : Reach M r v) : Escapes M v := by
  induction h with
  | refl => exact Escapes.root hr
  | tail _ hstep ih => exact Escapes.ref ih hstep

theorem escapes_of_reaches {v : V} (h : Reaches M v) : Escapes M v := by
  cases h with
  | intro r hr => exact escapes_of_reach M hr.1 hr.2

/-- Soundness of the engine's escape set: everything it flags really is reachable
from some object exposed at the isolation boundary. -/
theorem reaches_of_escapes {v : V} (h : Escapes M v) : Reaches M v := by
  induction h with
  | root hv => exact ⟨_, hv, Reach.refl⟩
  | ref _ hstep ih =>
      cases ih with
      | intro r hr => exact ⟨r, hr.1, hr.2.tail hstep⟩

/-- The escape set computed by the engine coincides, pointwise, with semantic
reachability from the isolation boundary. -/
theorem escapes_iff_reaches (v : V) : Escapes M v ↔ Reaches M v :=
  ⟨reaches_of_escapes M, escapes_of_reaches M⟩

/-! ### Kleene iteration: the engine's fixpoint is computed by finite iteration -/

/-- The `n`-th approximation produced by iterating the engine's transfer function
from the empty set. -/
def approx : Nat → V → Prop
  | 0 => fun _ => False
  | n + 1 => fun v => M.roots v ∨ ∃ u, approx n u ∧ M.ref u v

theorem approx_succ_of_approx {n : Nat} {v : V} (h : approx M n v) : approx M (n + 1) v := by
  induction n generalizing v with
  | zero => exact absurd h (by intro hf; exact hf)
  | succ n ih =>
      cases h with
      | inl hv => exact Or.inl hv
      | inr hu =>
          cases hu with
          | intro u hu => exact Or.inr ⟨u, ih hu.1, hu.2⟩

theorem approx_mono {n m : Nat} (hnm : n ≤ m) {v : V} (h : approx M n v) : approx M m v := by
  induction m with
  | zero =>
      have : n = 0 := Nat.le_zero.mp hnm
      exact this ▸ h
  | succ m ih =>
      cases Nat.lt_or_ge n (m + 1) with
      | inl hlt => exact approx_succ_of_approx M (ih (Nat.lt_succ_iff.mp hlt))
      | inr hge =>
          have : n = m + 1 := Nat.le_antisymm hnm hge
          exact this ▸ h

theorem escapes_of_approx {n : Nat} {v : V} (h : approx M n v) : Escapes M v := by
  induction n generalizing v with
  | zero => exact absurd h (by intro hf; exact hf)
  | succ n ih =>
      cases h with
      | inl hv => exact Escapes.root hv
      | inr hu =>
          cases hu with
          | intro u hu => exact Escapes.ref (ih hu.1) hu.2

theorem exists_approx_of_escapes {v : V} (h : Escapes M v) : ∃ n, approx M n v := by
  induction h with
  | root hv => exact ⟨1, Or.inl hv⟩
  | @ref u v _ hstep ih =>
      cases ih with
      | intro n hn => exact ⟨n + 1, Or.inr ⟨u, hn, hstep⟩⟩

/-- The engine's escape set is reached by finite Kleene iteration of its transfer
function. -/
theorem escapes_iff_exists_approx (v : V) : Escapes M v ↔ ∃ n, approx M n v := by
  constructor
  · exact exists_approx_of_escapes M
  · intro h
    cases h with
    | intro n hn => exact escapes_of_approx M hn

/-! ### Main result -/

/-- **Soundness and completeness of the isolation engine.**

The engine reports a null escape exactly when the model genuinely contains an
object that is reachable from the isolation boundary yet not owned by the
isolate. -/
theorem null_escape_iff_unowned_reachable : NullEscape M ↔ UnownedReachable M := by
  constructor
  · intro h
    cases h with
    | intro v hv => exact ⟨v, reaches_of_escapes M hv.1, hv.2⟩
  · intro h
    cases h with
    | intro v hv => exact ⟨v, escapes_of_reaches M hv.1, hv.2⟩

/-- Iterative form of the main result: the engine, run as a finite iteration,
reports a null escape exactly when some unowned object is reachable. -/
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


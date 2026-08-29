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
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

This module is deliberately self-contained (no `import`s), so that the header
comment above can be the very first thing in the file. The reachability relation
`PCA.Isolation.Escapes` defined below is the reflexive-transitive closure of a
policy's one-step relation, i.e. the analogue of Mathlib's
`Relation.ReflTransGen`; the target theorem `priv_escape_monotone` is the
analogue of Mathlib's `Relation.ReflTransGen.mono`, reproved here from scratch.
-/

set_option autoImplicit false

namespace PCA.Isolation

universe u

/-- An isolation policy on a type of privilege states `S` is given by a one-step
privilege-transfer relation `step`: `step a b` means that a principal holding
privilege state `a` is permitted, in one step, to move to privilege state `b`. -/
structure Policy (S : Type u) where
  /-- The permitted one-step privilege transfers. -/
  step : S → S → Prop

/-- Policy `q` is *at least as permissive* as policy `p` when it allows every
step that `p` allows. -/
def Permits {S : Type u} (p q : Policy S) : Prop :=
  ∀ a b : S, p.step a b → q.step a b

/-- `Escapes p a b` says that, under policy `p`, a principal starting in privilege
state `a` can reach privilege state `b` by a finite (possibly empty) sequence of
permitted steps. This is the reachability semantics of the isolation engine: it
is the reflexive-transitive closure of `p.step`. -/
inductive Escapes {S : Type u} (p : Policy S) : S → S → Prop
  /-- No escape needed: every state reaches itself. -/
  | refl (a : S) : Escapes p a a
  /-- Extend an escape by one further permitted step. -/
  | tail {a b c : S} : Escapes p a b → p.step b c → Escapes p a c

/-- The set (as a predicate) of privilege states reachable from `a` under `p`. -/
def Reach {S : Type u} (p : Policy S) (a : S) : S → Prop :=
  fun b => Escapes p a b

variable {S : Type u} {p q : Policy S}

theorem Escapes.single {a b : S} (h : p.step a b) : Escapes p a b :=
  (Escapes.refl a).tail h

theorem Escapes.trans {a b c : S} (hab : Escapes p a b) (hbc : Escapes p b c) :
    Escapes p a c := by
  induction hbc with
  | refl => exact hab
  | tail _ hstep ih => exact ih.tail hstep

theorem Permits.rfl (p : Policy S) : Permits p p := fun _ _ h => h

theorem Permits.trans {r : Policy S} (hpq : Permits p q) (hqr : Permits q r) :
    Permits p r := fun a b h => hqr a b (hpq a b h)

/-- **Privilege escape is monotone in the policy.**

If policy `q` permits every single step that policy `p` permits, then every
privilege escape realizable under `p` is also realizable under `q`.

This is the monotonicity component of the soundness of the isolation engine's
model: relaxing the one-step permissions can only enlarge the set of reachable
privilege states, never shrink it.

It is the analogue, for the reachability relation `Escapes`, of Mathlib's
`Relation.ReflTransGen.mono`. -/
theorem priv_escape_monotone (hpq : Permits p q) {a b : S} (hab : Escapes p a b) :
    Escapes q a b := by
  induction hab with
  | refl => exact Escapes.refl _
  | tail _ hstep ih => exact ih.tail (hpq _ _ hstep)

/-- Set-level form of monotonicity: the reachable set grows with the policy. -/
theorem reach_mono (hpq : Permits p q) (a : S) : ∀ b : S, Reach p a b → Reach q a b :=
  fun _ hb => priv_escape_monotone hpq hb

/-- Contrapositive (isolation-preservation) form: if `b` is unreachable under the
more permissive policy `q`, then it is unreachable under `p` as well. -/
theorem not_escapes_of_not_escapes (hpq : Permits p q) {a b : S}
    (hb : ¬ Escapes q a b) : ¬ Escapes p a b :=
  fun hab => hb (priv_escape_monotone hpq hab)

end PCA.Isolation


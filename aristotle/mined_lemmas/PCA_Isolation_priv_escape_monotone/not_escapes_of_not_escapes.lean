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

theorem not_escapes_of_not_escapes (hpq : Permits p q) {a b : S}
    (hb : ¬ Escapes q a b) : ¬ Escapes p a b :=
  fun hab => hb (priv_escape_monotone hpq hab)

end PCA.Isolation


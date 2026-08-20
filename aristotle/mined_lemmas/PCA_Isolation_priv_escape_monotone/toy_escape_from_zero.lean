/-
# Priv Escape Monotone
Category: Proof-Carrying Apps
Target: PCA.Isolation.priv_escape_monotone
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace PCA.Isolation

/-- An isolation policy over a type of capabilities `Cap`.

A rule `(pre, c) ∈ rules` says: a sandboxed component that already holds every
capability in the precondition set `pre` can additionally obtain `c`. -/
structure Policy (Cap : Type*) where
  /-- The derivation rules of the policy. -/
  rules : Set (Set Cap × Cap)

variable {Cap : Type*}

/-- `Reach P G c` : starting from the initially granted capabilities `G`, the
isolation engine's model allows the component to obtain capability `c`. -/
inductive Reach (P : Policy Cap) (G : Set Cap) : Cap → Prop
  /-- Anything initially granted is reachable. -/
  | base {c : Cap} (hc : c ∈ G) : Reach P G c
  /-- A rule fires once all of its preconditions are reachable. -/
  | step {pre : Set Cap} {c : Cap} (hr : (pre, c) ∈ P.rules)
      (hpre : ∀ d ∈ pre, Reach P G d) : Reach P G c

/-- The set of capabilities reachable from the initial grant set `G`. -/

theorem toy_escape_from_zero : PrivEscape toyPolicy {2} ({0} : Set (Fin 3)) :=
  ⟨2, rfl, Reach.step (by simp [toyPolicy]) fun _ hd => Reach.base hd⟩

/-- With no capabilities granted, the toy sandbox is safe: no escape occurs.
Hence `priv_escape_monotone` is not vacuously true. -/

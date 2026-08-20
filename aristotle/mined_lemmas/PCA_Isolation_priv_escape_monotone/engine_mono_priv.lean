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

namespace PCA
namespace Isolation

/-! ## The isolation model

A *capability* is an abstract resource token held by a sandboxed component.
A *policy* describes the delegation edges of the isolation engine: `pol.grant c d`
means that a component already holding capability `c` may acquire capability `d`.

The privilege set of a component is the set of capabilities it starts with; the
component *escapes* to a capability `t` if it can acquire `t` through some finite
chain of grants. -/

/-- Capabilities are identified by natural numbers. -/
abbrev Cap : Type := ℕ

/-- An isolation policy: the delegation edges available to the sandboxed component. -/
structure Policy where
  /-- `grant c d` : holding capability `c` permits acquiring capability `d`. -/
  grant : Cap → Cap → Prop

/-- `Reach pol P` is the set of capabilities obtainable from the initial privilege
set `P` by finitely many delegation steps of the policy `pol`. -/
inductive Reach (pol : Policy) (P : Set Cap) : Cap → Prop
  | base {c : Cap} : c ∈ P → Reach pol P c
  | step {c d : Cap} : Reach pol P c → pol.grant c d → Reach pol P d

/-- A component with privilege set `P` *escapes* to the capability `t` when `t` is
reachable from `P` under the policy. -/

theorem engine_mono_priv (pol : Policy) {P Q : Set Cap} (h : P ⊆ Q) (n : ℕ) :
    engine pol P n ⊆ engine pol Q n := by
  induction n with
  | zero => simpa [engine] using h
  | succ k ih => exact stepSet_mono pol ih

/-! ## Soundness and completeness of the engine -/

/-- **Soundness**: everything the engine reports as obtainable really is reachable. -/

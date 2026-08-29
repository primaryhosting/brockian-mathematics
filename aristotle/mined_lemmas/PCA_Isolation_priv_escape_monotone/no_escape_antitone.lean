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
-/

set_option autoImplicit false

namespace PCA.Isolation

universe u v

/-- A configuration of the isolation engine: `c d p` says that domain `d` currently
holds privilege `p`. -/
abbrev Config (Dom : Type u) (Priv : Type v) : Type max u v := Dom → Priv → Prop

/-- The configuration obtained from `c` by granting privilege `p` to domain `d`. -/

theorem no_escape_antitone {Dom : Type u} {Priv : Type v} {P Q : Policy Dom Priv}
    (hPQ : P.Le Q) {c : Config Dom Priv} {d : Dom} {p : Priv} (h : ¬ Escapes Q c d p) :
    ¬ Escapes P c d p :=
  fun hP => h (priv_escape_monotone hPQ hP)

/-! ## A concrete instance: the implication is strict

The following witnesses show that the model is inhabited in a non-degenerate way:
privilege escapes really do occur under a permissive policy, and the converse of
`priv_escape_monotone` fails. -/

/-- The empty configuration on one domain and one privilege. -/

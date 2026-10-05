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

def Policy.Le {Dom : Type u} {Priv : Type v} (P Q : Policy Dom Priv) : Prop :=
  ∀ c d p, P.grant c d p → Q.grant c d p

/-- Reachability of configurations under a policy: the reflexive-transitive closure
of the permitted single-step grants. -/
inductive Reach {Dom : Type u} {Priv : Type v} (P : Policy Dom Priv) :
    Config Dom Priv → Config Dom Priv → Prop
  | refl (c : Config Dom Priv) : Reach P c c
  | step {c c' : Config Dom Priv} {d : Dom} {p : Priv} :
      Reach P c c' → P.grant c' d p → Reach P c (grantAt c' d p)

/-- A privilege escape: starting from `c`, the engine can reach a configuration in
which domain `d` holds privilege `p`, even though it did not hold it initially. -/

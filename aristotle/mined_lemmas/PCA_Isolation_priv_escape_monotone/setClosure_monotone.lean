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

universe u

namespace PCA
namespace Isolation

/-- A set of capabilities, represented by its membership predicate. -/
abbrev CapSet (Cap : Type u) : Type u := Cap → Prop

/-- `g₁ ≼ g₂` : every capability granted by `g₁` is also granted by `g₂`. -/

theorem setClosure_monotone (rules : Set (SetRule Cap)) :
    Monotone (setClosure rules) :=
  fun _ _ hg _ hc => setEscapes_of_subset hg hc

/-- The closure operator is extensive. -/

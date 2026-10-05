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

theorem reach_mono_rules {Cap : Type u} {rules₁ rules₂ : Rule Cap → Prop}
    (hr : ∀ r, rules₁ r → rules₂ r) {g : CapSet Cap} {c : Cap} (h : Reach rules₁ g c) :
    Reach rules₂ g c := by
  induction h with
  | base hc => exact Reach.base hc
  | step hrule _ ih => exact Reach.step (hr _ hrule) ih

/-- Soundness/completeness of the closure as the least fixed point: `closure rules g`
is contained in every grant set that contains `g` and is closed under the rules. -/

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

def CapSubset {Cap : Type u} (g₁ g₂ : CapSet Cap) : Prop := ∀ c, g₁ c → g₂ c

@[inherit_doc] scoped infix:50 " ≼ " => CapSubset

/-- A *derivation rule* of the isolation engine: holding all capabilities in the
premise set `r.1` lets an application obtain the capability `r.2`. -/
abbrev Rule (Cap : Type u) : Type u := CapSet Cap × Cap

/-- `Reach rules g c` says that an application initially granted the capabilities
`g` can, using the engine's derivation `rules`, come to hold the capability `c`. -/
inductive Reach {Cap : Type u} (rules : Rule Cap → Prop) (g : CapSet Cap) : Cap → Prop
  /-- Every granted capability is held. -/
  | base {c : Cap} (hc : g c) : Reach rules g c
  /-- A rule fires once all of its premises are held. -/
  | step {pre : CapSet Cap} {c : Cap} (hr : rules (pre, c))
      (hpre : ∀ x, pre x → Reach rules g x) : Reach rules g c

/-- The set of capabilities an application with grants `g` can end up holding. -/

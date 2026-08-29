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
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA
namespace WriteIntegrity

/-! ## The isolation engine's write model -/

/-- Principals (subjects) of the isolation engine. -/
abbrev Principal := Nat

/-- Memory addresses of the isolated store. -/
abbrev Addr := Nat

/-- Values that can be stored. -/
abbrev Val := Nat

/-- A write request: a principal asks to store `val` at `addr`. -/
structure Write where
  principal : Principal
  addr : Addr
  val : Val
deriving DecidableEq, Repr

/-- The state of the isolated store. -/
abbrev Mem := Addr → Val

/-- Point update of the store. -/

@[simp] theorem store_self (m : Mem) (a : Addr) (v : Val) : store m a v a = v := by
  simp [store]

/-- An access-control policy assigns to each address its owning principal. -/
structure Policy where
  owner : Addr → Principal

/-- A write is *authorized* by the policy when its issuer owns the target address. -/

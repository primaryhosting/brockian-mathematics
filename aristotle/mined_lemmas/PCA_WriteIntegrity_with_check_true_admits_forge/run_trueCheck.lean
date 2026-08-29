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

/-! ## The isolation engine's model

A *proof-carrying app* issues writes to a shared store.  The isolation engine
mediates every write through a `check` predicate: the write is applied only if
the check accepts it.  The intended check is the *capability check*, which
accepts a write exactly when the writing principal holds a capability for the
target address.

We formalise the engine, prove that the capability check is sound (it enforces
the write-integrity policy), and prove the target result: the degenerate engine
whose check is constantly `true` admits a *forge* — a write with no backing
capability that nonetheless mutates the store — so it is unsound. -/

/-- Memory addresses of the shared store. -/
abbrev Addr := Nat

/-- Values held in the shared store. -/
abbrev Val := Nat

/-- Identities that may issue writes. -/
abbrev Principal := Nat

/-- A capability: principal `owner` is permitted to write address `addr`. -/
structure Cap where
  owner : Principal
  addr : Addr
deriving DecidableEq, Repr

/-- A write request: principal `principal` asks to store `val` at `addr`. -/
structure Write where
  principal : Principal
  addr : Addr
  val : Val
deriving DecidableEq, Repr

/-- The shared store. -/
abbrev State := Addr → Val

/-- A write is *authorized* by a capability list when some capability in the
list grants its principal access to its address. -/

theorem run_trueCheck (caps : List Cap) :
    ∀ (ws : List Write) (st : State),
      run trueCheck caps st ws = ws.foldl applyWrite st := by
  intro ws
  induction ws with
  | nil => intro st; simp
  | cons w ws ih => intro st; simp [ih]

/-! ## The forge -/

/-- A forged write: principal `0` writing `1` to address `0`. -/

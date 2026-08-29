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

theorem trivial_foldl (ws : List Write) :
    ∀ (m : Mem) (log : List Write),
      ws.foldl trivialEngine.step (m, log) = (applyAll m ws, log ++ ws) := by
  induction ws with
  | nil => intro m log; simp [applyAll]
  | cons w ws ih =>
    intro m log
    have hstep : trivialEngine.step (m, log) w
        = (store m w.addr w.val, log ++ [w]) := by
      simp [Engine.step, trivialEngine]
    simp only [List.foldl_cons, hstep, ih, applyAll, List.append_assoc,
      List.cons_append, List.nil_append]

/-- With the constantly-true check, the audit log of a run is exactly the input trace. -/

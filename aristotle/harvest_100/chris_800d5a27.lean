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

/-- Agents (principals) of the isolation engine. -/
abbrev Agent : Type := Nat

/-- Addresses of the guarded store. -/
abbrev Addr : Type := Nat

/-- Values that may be written. -/
abbrev Val : Type := Nat

/-- A write request: a principal asks to put a value at an address. -/
structure Write where
  agent : Agent
  addr : Addr
  val : Val
deriving DecidableEq

/-- A write policy: for each address, the predicate telling which principals are
allowed to write it (the address' ACL). -/
abbrev Policy : Type := Addr → Agent → Prop

/-- A write is *authorized* when its issuing agent lies in the policy's ACL for the
target address. -/
def Authorized (P : Policy) (w : Write) : Prop := P w.addr w.agent

/-- A *check* is the decision procedure the isolation engine runs on each write. -/
abbrev Check : Type := Write → Bool

/-- The engine *admits* a write exactly when its check accepts it. -/
def Admits (c : Check) (w : Write) : Prop := c w = true

/-- The degenerate check that accepts everything. -/
def checkTrue : Check := fun _ => true

/-- The check induced by a (decidable) policy: accept exactly the authorized writes. -/
def checkOf (P : Policy) [∀ w : Write, Decidable (Authorized P w)] : Check :=
  fun w => decide (Authorized P w)

/-- **Write integrity**: the engine admits only authorized writes. -/
def HasWriteIntegrity (P : Policy) (c : Check) : Prop :=
  ∀ w : Write, Admits c w → Authorized P w

/-- A *forge* is a write that the engine admits even though the policy forbids it. -/
def Forges (P : Policy) (c : Check) (w : Write) : Prop :=
  Admits c w ∧ ¬ Authorized P w

/-- The policy-induced check does enjoy write integrity: it is a sound reference point,
against which the degenerate check below is a genuine failure. -/
theorem checkOf_hasWriteIntegrity (P : Policy) [∀ w : Write, Decidable (Authorized P w)] :
    HasWriteIntegrity P (checkOf P) := by
  intro w hw
  exact of_decide_eq_true hw

/-- **Main result.** If some write `w` is unauthorized under the policy `P`, then the
degenerate check `checkTrue` admits `w`, so `w` is a forge, and consequently `checkTrue`
does not enjoy write integrity for `P`. -/
theorem with_check_true_admits_forge (P : Policy) (w : Write) (hw : ¬ Authorized P w) :
    Forges P checkTrue w ∧ ¬ HasWriteIntegrity P checkTrue :=
  ⟨⟨rfl, hw⟩, fun hInt => hw (hInt w rfl)⟩

/-- A concrete instance: with an everywhere-empty ACL every write is unauthorized, yet
`checkTrue` admits it. -/
example (w : Write) : Forges (fun _ _ => False) checkTrue w :=
  (with_check_true_admits_forge (fun _ _ => False) w (fun h => h)).1

end WriteIntegrity
end PCA

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


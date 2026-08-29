/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA
namespace WriteIntegrity

/-- A write request issued by an actor against a storage target, carrying a
capability token that is supposed to justify the write. -/
structure Write where
  /-- The principal issuing the write. -/
  actor : Nat
  /-- The storage object being written. -/
  target : Nat
  /-- The capability token presented with the write. -/
  token : Nat
deriving DecidableEq, Repr

/-- A write-integrity policy: each target has an owner, and each actor has a
set of valid capability tokens. -/
structure Policy where
  /-- Owner of each target. -/
  owner : Nat → Nat
  /-- Which tokens are valid for a given actor. -/
  validToken : Nat → Nat → Bool

/-- A write is authorized when it is issued by the owner of the target and
carries a token valid for that actor. -/
def Policy.authorizes (P : Policy) (w : Write) : Bool :=
  (P.owner w.target == w.actor) && P.validToken w.actor w.token

/-- The isolation engine's admission check on write requests. -/
abbrev Check := Write → Bool

/-- The engine accepts a write exactly when its check returns `true`. -/
def Accepts (chk : Check) (w : Write) : Prop := chk w = true

/-- Write-integrity soundness: every accepted write is authorized by the policy. -/
def Sound (P : Policy) (chk : Check) : Prop :=
  ∀ w : Write, Accepts chk w → P.authorizes w = true

/-- The engine admits a forge if some unauthorized write is nevertheless accepted. -/
def AdmitsForge (P : Policy) (chk : Check) : Prop :=
  ∃ w : Write, Accepts chk w ∧ P.authorizes w = false

/-- The degenerate check that accepts everything. -/
def trivialCheck : Check := fun _ => true

/-- A concrete forged write against target `0`: it is issued by a principal
that is not the owner of target `0`. -/
def forgedWrite (P : Policy) : Write :=
  { actor := P.owner 0 + 1, target := 0, token := 0 }

/-- The concrete forged write is never authorized. -/
theorem authorizes_forgedWrite (P : Policy) : P.authorizes (forgedWrite P) = false := by
  simp [Policy.authorizes, forgedWrite, Nat.succ_ne_self]

/-- An engine whose admission check is constantly `true` admits a forge against
*every* write-integrity policy, and is therefore never sound. -/
theorem with_check_true_admits_forge (P : Policy) :
    AdmitsForge P trivialCheck ∧ ¬ Sound P trivialCheck := by
  have hforge : AdmitsForge P trivialCheck :=
    ⟨forgedWrite P, rfl, authorizes_forgedWrite P⟩
  refine ⟨hforge, ?_⟩
  intro hsound
  obtain ⟨w, hacc, hbad⟩ := hforge
  have hgood := hsound w hacc
  rw [hgood] at hbad
  exact Bool.noConfusion hbad

/-- By contrast, the check that simply enforces the policy is sound. -/
theorem policy_check_sound (P : Policy) : Sound P (fun w => P.authorizes w) :=
  fun _ h => h

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


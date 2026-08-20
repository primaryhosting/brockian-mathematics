/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace PCA.WriteIntegrity

/-- A write request submitted to the isolation engine: the resource has a declared
`owner`, the request is signed by `signer`, and carries a `payload`. -/
structure Write where
  /-- Principal that owns the target resource. -/
  owner : Nat
  /-- Principal that signed (issued) this write request. -/
  signer : Nat
  /-- The targeted resource. -/
  resource : Nat
  /-- The data to be written. -/
  payload : Nat
  deriving DecidableEq

/-- The integrity policy of the model: a write is authorized exactly when the signer of
the request is the owner of the resource. -/
def Authorized (w : Write) : Prop := w.signer = w.owner

/-- A forged write is one that violates the integrity policy. -/
def Forged (w : Write) : Prop := ¬ Authorized w

/-- A checker is *sound* for write integrity when everything it accepts is authorized. -/
def Sound (check : Write → Bool) : Prop := ∀ w : Write, check w = true → Authorized w

/-- A checker *admits a forge* when it accepts some write that violates the policy. -/
def AdmitsForge (check : Write → Bool) : Prop := ∃ w : Write, check w = true ∧ Forged w

/-- The degenerate checker that accepts every write. -/
def alwaysTrue : Write → Bool := fun _ => true

/-- A concrete forged write: resource owned by principal `0`, but signed by principal `1`. -/
def forgedWrite : Write := { owner := 0, signer := 1, resource := 0, payload := 0 }

/-- Key intermediate lemma: `forgedWrite` really is forged, i.e. it is not authorized. -/
theorem forgedWrite_forged : Forged forgedWrite := by
  intro h
  exact Nat.succ_ne_zero 0 h

/-- Any checker admitting a forge fails to be sound. -/
theorem not_sound_of_admitsForge {check : Write → Bool} (h : AdmitsForge check) :
    ¬ Sound check := by
  rintro hs
  obtain ⟨w, hw, hforge⟩ := h
  exact hforge (hs w hw)

/-- **With check true admits forge.**  The checker that returns `true` on every write
accepts a forged write, and consequently is not sound for write integrity. -/
theorem with_check_true_admits_forge :
    AdmitsForge alwaysTrue ∧ ¬ Sound alwaysTrue := by
  have hforge : AdmitsForge alwaysTrue :=
    ⟨forgedWrite, rfl, forgedWrite_forged⟩
  exact ⟨hforge, not_sound_of_admitsForge hforge⟩

end PCA.WriteIntegrity

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


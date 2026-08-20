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

theorem not_sound_of_admitsForge {check : Write → Bool} (h : AdmitsForge check) :
    ¬ Sound check := by
  rintro hs
  obtain ⟨w, hw, hforge⟩ := h
  exact hforge (hs w hw)

/-- **With check true admits forge.**  The checker that returns `true` on every write
accepts a forged write, and consequently is not sound for write integrity. -/

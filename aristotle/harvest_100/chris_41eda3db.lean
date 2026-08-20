/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.WriteIntegrity

/-- A write request submitted to the isolation engine: a claimed author, a
payload, and an integrity token that is supposed to certify the pair. -/
structure Write where
  author : Nat
  payload : Nat
  token : Nat
  deriving DecidableEq

/-- The integrity token that a genuine author would attach to a write. -/
def expected (w : Write) : Nat := w.author + w.payload

/-- A write is *authentic* when its token is the one a genuine author would
have produced. -/
def Authentic (w : Write) : Prop := w.token = expected w

/-- The engine admits a write exactly when the policy `check` says so. -/
def Accepts (check : Write → Bool) (w : Write) : Prop := check w = true

/-- A *forgery* for a policy is an inauthentic write that the policy
nonetheless admits. -/
def Forges (check : Write → Bool) (w : Write) : Prop :=
  Accepts check w ∧ ¬ Authentic w

/-- Write-integrity soundness: every admitted write is authentic. -/
def Sound (check : Write → Bool) : Prop := ∀ w, Accepts check w → Authentic w

/-- The degenerate policy that admits every write. -/
def checkTrue : Write → Bool := fun _ => true

/-- The honest policy: recompute the expected token and compare. -/
def checkToken : Write → Bool := fun w => decide (w.token = expected w)

/-- **Main result.** The always-true check admits a forgery, and hence is not a
sound write-integrity policy. -/
theorem with_check_true_admits_forge :
    (∃ w : Write, Forges checkTrue w) ∧ ¬ Sound checkTrue := by
  have hforge : Forges checkTrue ⟨0, 0, 1⟩ := by
    refine ⟨rfl, ?_⟩
    intro h
    have hne : ¬ ((1 : Nat) = 0 + 0) := by decide
    exact hne h
  exact ⟨⟨_, hforge⟩, fun hs => hforge.2 (hs _ hforge.1)⟩

/-- For contrast: the honest token check *is* sound, so the failure above is a
property of the degenerate policy, not of the model itself. -/
theorem checkToken_sound : Sound checkToken := by
  intro w hw
  have h : w.token = expected w := of_decide_eq_true hw
  exact h

/-- Soundness and the existence of a forgery are exactly incompatible. -/
theorem sound_iff_no_forge (check : Write → Bool) :
    Sound check ↔ ¬ ∃ w, Forges check w := by
  constructor
  · rintro hs ⟨w, hacc, hna⟩
    exact hna (hs w hacc)
  · intro h w hacc
    exact Classical.byContradiction fun hna => h ⟨w, hacc, hna⟩

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


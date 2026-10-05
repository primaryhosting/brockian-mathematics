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

/-- A write request submitted to the isolation engine: it targets a memory
`region`, carries a `payload`, and presents a capability `token` that is meant
to justify the access. -/
structure Write where
  region : Nat
  payload : Nat
  token : Nat
  deriving DecidableEq, Repr

/-- A write policy: `pol r t = true` means capability token `t` authorizes
writes to region `r`. -/
abbrev Policy := Nat → Nat → Bool

/-- A checker is the (decidable) admission test the engine actually runs on a
write request. -/
abbrev Checker := Write → Bool

/-- A write is *genuine* under `pol` when the token it presents really does
authorize the region it targets. -/
def Genuine (pol : Policy) (w : Write) : Prop := pol w.region w.token = true

/-- A write is a *forgery* under `pol` when it is not genuine: the presented
token does not authorize the targeted region. -/
def Forged (pol : Policy) (w : Write) : Prop := ¬ Genuine pol w

/-- The engine admits `w` when the checker accepts it. -/
def Admits (c : Checker) (w : Write) : Prop := c w = true

/-- Soundness of a checker relative to a policy: every admitted write is
genuine, i.e. no forgery is ever let through. -/
def Sound (pol : Policy) (c : Checker) : Prop := ∀ w, Admits c w → Genuine pol w

/-- Completeness of a checker relative to a policy: every genuine write is
admitted. -/
def Complete (pol : Policy) (c : Checker) : Prop := ∀ w, Genuine pol w → Admits c w

/-- The degenerate checker that returns `true` on every write ("check := true"). -/
def trueCheck : Checker := fun _ => true

/-- The reference checker, which consults the policy. -/
def refCheck (pol : Policy) : Checker := fun w => pol w.region w.token

@[simp] theorem trueCheck_admits (w : Write) : Admits trueCheck w := rfl

/-- Genuineness is decidable, so every write is either genuine or forged. -/
theorem genuine_or_forged (pol : Policy) (w : Write) :
    Genuine pol w ∨ Forged pol w :=
  match h : pol w.region w.token with
  | true => Or.inl h
  | false => Or.inr (fun hg => Bool.noConfusion (h.symm.trans hg))

/-- The constant-`true` checker is sound exactly when the policy authorizes
*every* write, i.e. when there is nothing to protect. -/
theorem sound_trueCheck_iff (pol : Policy) :
    Sound pol trueCheck ↔ ∀ w, Genuine pol w := by
  constructor
  · intro h w
    exact h w (trueCheck_admits w)
  · intro h w _
    exact h w

/-- **Main result.** If any forgery exists at all under the policy `pol`, then
the engine instantiated with the constant-`true` check admits that forgery, and
is therefore unsound. -/
theorem with_check_true_admits_forge (pol : Policy) (h : ∃ w, Forged pol w) :
    (∃ w, Forged pol w ∧ Admits trueCheck w) ∧ ¬ Sound pol trueCheck := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨w, hw, trueCheck_admits w⟩, ?_⟩
  intro hs
  exact hw ((sound_trueCheck_iff pol).mp hs w)

/-- The hypothesis of the main theorem is satisfiable: under the deny-all
policy every write is a forgery, so the constant-`true` check is unsound. -/
theorem denyAll_forge_exists : ∃ w, Forged (fun _ _ => false) w :=
  ⟨⟨0, 0, 0⟩, by simp [Forged, Genuine]⟩

theorem not_sound_trueCheck_denyAll : ¬ Sound (fun _ _ => false) trueCheck :=
  (with_check_true_admits_forge _ denyAll_forge_exists).2

/-- By contrast, the reference checker that consults the policy is both sound
and complete, so the failure above is genuinely caused by replacing the check
with `true`. -/
theorem refCheck_sound_and_complete (pol : Policy) :
    Sound pol (refCheck pol) ∧ Complete pol (refCheck pol) := by
  constructor
  · intro w hw
    exact hw
  · intro w hw
    exact hw

/-- The constant-`true` checker is, however, complete: it never rejects a
genuine write. Unsoundness is the whole of its failure. -/
theorem complete_trueCheck (pol : Policy) : Complete pol trueCheck :=
  fun w _ => trueCheck_admits w

end WriteIntegrity
end PCA


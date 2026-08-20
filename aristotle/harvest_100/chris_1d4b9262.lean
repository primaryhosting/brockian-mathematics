/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required file header is a module doc comment, which Lean requires to come
-- after any `import` lines; to keep the header literally first we develop this file over
-- Lean 4 core only (no imports are needed for the argument below).

namespace PCA
namespace WriteIntegrity

/-- A write request submitted to the isolation engine: the claimed author,
the capability token presented with the request, and the payload. -/
structure Write where
  author : Nat
  token : Nat
  payload : Nat
  deriving DecidableEq

/-- A write is *authorized* (w.r.t. the key assignment `keyOf`) when the presented
token really is the claimed author's capability key. -/
def Authorized (keyOf : Nat → Nat) (w : Write) : Prop := w.token = keyOf w.author

/-- An admission engine is a decision procedure on write requests. -/
abbrev Engine := Write → Bool

/-- The engine admits a write exactly when its check returns `true`. -/
def Admits (e : Engine) (w : Write) : Prop := e w = true

/-- The engine is *sound* for write integrity when everything it admits is authorized. -/
def Sound (keyOf : Nat → Nat) (e : Engine) : Prop := ∀ w, Admits e w → Authorized keyOf w

/-- The degenerate engine whose check always succeeds. -/
def checkTrue : Engine := fun _ => true

/--
**With check `true`, the engine admits a forgery.**

For every key assignment `keyOf`, the engine that accepts every request admits a write
whose token is not the claimed author's key; consequently that engine is not sound for
write integrity.
-/
theorem with_check_true_admits_forge (keyOf : Nat → Nat) :
    (∃ w : Write, Admits checkTrue w ∧ ¬ Authorized keyOf w) ∧ ¬ Sound keyOf checkTrue := by
  have hforge : ∃ w : Write, Admits checkTrue w ∧ ¬ Authorized keyOf w := by
    refine ⟨⟨0, keyOf 0 + 1, 0⟩, rfl, ?_⟩
    intro h
    exact Nat.succ_ne_self (keyOf 0) h
  refine ⟨hforge, ?_⟩
  intro hsound
  obtain ⟨w, hadm, hnauth⟩ := hforge
  exact hnauth (hsound w hadm)

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


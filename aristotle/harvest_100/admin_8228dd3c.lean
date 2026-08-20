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

namespace PCA.WriteIntegrity

/-- A write request submitted to the isolation engine: a payload together with
an integrity tag that is supposed to authenticate it. -/
structure Write where
  /-- The data being written. -/
  payload : Nat
  /-- The integrity tag accompanying the write. -/
  tag : Nat
  deriving DecidableEq

/-- A write is *authentic* for the secret `key` when its tag is the correct
MAC of its payload (here modelled as `key + payload`). -/
def Authentic (key : Nat) (w : Write) : Prop := w.tag = key + w.payload

/-- The engine's admission rule: a write is admitted exactly when the
integrity `check` returns `true` on it. -/
def Admits (check : Write → Bool) (w : Write) : Prop := check w = true

/-- Write-integrity soundness for a given check: every admitted write is
authentic. -/
def Sound (key : Nat) (check : Write → Bool) : Prop :=
  ∀ w : Write, Admits check w → Authentic key w

/-- The check that returns `true` on every write (i.e. no checking at all). -/
def checkTrue : Write → Bool := fun _ => true

/-- **With the always-true check, the engine admits a forgery.**

Replacing the integrity check by the constantly-`true` check destroys write
integrity: for every key there is a write that the engine admits although it is
not authentic, hence `Sound key checkTrue` fails.

The arithmetic core is closed by the library lemma `Nat.succ_ne_self`. -/
theorem with_check_true_admits_forge (key : Nat) :
    (∃ w : Write, Admits checkTrue w ∧ ¬ Authentic key w) ∧ ¬ Sound key checkTrue := by
  have hforge : Admits checkTrue ⟨0, key + 1⟩ ∧ ¬ Authentic key ⟨0, key + 1⟩ := by
    refine ⟨rfl, ?_⟩
    intro h
    simp only [Authentic] at h
    exact Nat.succ_ne_self key h
  refine ⟨⟨⟨0, key + 1⟩, hforge⟩, ?_⟩
  intro hs
  exact hforge.2 (hs _ hforge.1)

end PCA.WriteIntegrity


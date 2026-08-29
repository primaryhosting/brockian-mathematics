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

universe u v w t

/-- A write request submitted to the isolation engine: a principal asks to write
a value at a path, presenting an authorization token (the "proof" it carries). -/
structure Request (Principal : Type u) (Path : Type v) (Value : Type w)
    (Token : Type t) where
  principal : Principal
  path : Path
  value : Value
  token : Token

variable {Principal : Type u} {Path : Type v} {Value : Type w} {Token : Type t}

/-- A write policy: the set of requests that *ought* to be admitted. -/
abbrev Policy (Principal : Type u) (Path : Type v) (Value : Type w) (Token : Type t) :=
  Request Principal Path Value Token → Prop

/-- The isolation engine's write-integrity monitor: a decision procedure on requests. -/
structure Engine (Principal : Type u) (Path : Type v) (Value : Type w)
    (Token : Type t) where
  check : Request Principal Path Value Token → Bool

/-- The engine admits (i.e. performs) a request exactly when its check succeeds. -/
def Engine.Admits (E : Engine Principal Path Value Token)
    (r : Request Principal Path Value Token) : Prop :=
  E.check r = true

/-- A *forge* is a request that the engine admits even though the policy forbids it. -/
def Forge (pol : Policy Principal Path Value Token)
    (E : Engine Principal Path Value Token)
    (r : Request Principal Path Value Token) : Prop :=
  E.Admits r ∧ ¬ pol r

/-- Write integrity (soundness): every admitted request is authorized by the policy. -/
def Sound (pol : Policy Principal Path Value Token)
    (E : Engine Principal Path Value Token) : Prop :=
  ∀ r, E.Admits r → pol r

/-- The engine built from a token verifier together with a `bypass` flag: when
`bypass = true` the check is trivially satisfied, short-circuiting verification. -/
def engineOf (bypass : Bool) (verify : Request Principal Path Value Token → Bool) :
    Engine Principal Path Value Token :=
  ⟨fun r => bypass || verify r⟩

/-- Write integrity fails exactly when the engine admits some forge. -/
theorem not_sound_iff_exists_forge (pol : Policy Principal Path Value Token)
    (E : Engine Principal Path Value Token) :
    ¬ Sound pol E ↔ ∃ r, Forge pol E r := by
  constructor
  · intro h
    refine Classical.byContradiction (fun hno => h (fun r hr => ?_))
    exact Classical.byContradiction (fun hp => hno ⟨r, hr, hp⟩)
  · intro h hs
    match h with
    | ⟨r, hr, hp⟩ => exact hp (hs r hr)

/-- **With the check set to `true`, the engine admits a forge.**

If the write-integrity check is trivially satisfied (`bypass = true`, so the
monitor short-circuits token verification and admits every request), then any
policy forbidding at least one request is violated: the forbidden request is a
forge that the engine admits, and hence the engine is not sound. -/
theorem with_check_true_admits_forge
    (pol : Policy Principal Path Value Token)
    (verify : Request Principal Path Value Token → Bool)
    (bypass : Bool) (hb : bypass = true)
    (r : Request Principal Path Value Token) (hr : ¬ pol r) :
    Forge pol (engineOf bypass verify) r ∧ ¬ Sound pol (engineOf bypass verify) := by
  have hadm : (engineOf bypass verify).Admits r := by
    cases bypass with
    | true => rfl
    | false => exact absurd hb (by simp)
  refine ⟨⟨hadm, hr⟩, ?_⟩
  rw [not_sound_iff_exists_forge]
  exact ⟨r, hadm, hr⟩

/-- Contrast: with the bypass off, the engine is sound as soon as the token
verifier only accepts policy-authorized requests. -/
theorem sound_of_verify_sound
    (pol : Policy Principal Path Value Token)
    (verify : Request Principal Path Value Token → Bool)
    (hv : ∀ r, verify r = true → pol r) :
    Sound pol (engineOf false verify) := by
  intro r hr
  have hvr : verify r = true := by
    have : (false || verify r) = true := hr
    simpa using this
  exact hv r hvr

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


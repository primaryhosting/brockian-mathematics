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

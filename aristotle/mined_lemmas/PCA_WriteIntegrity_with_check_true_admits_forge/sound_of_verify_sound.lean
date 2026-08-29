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


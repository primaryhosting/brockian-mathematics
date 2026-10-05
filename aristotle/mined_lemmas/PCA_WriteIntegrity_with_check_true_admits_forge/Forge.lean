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

def Forge (pol : Policy Principal Path Value Token)
    (E : Engine Principal Path Value Token)
    (r : Request Principal Path Value Token) : Prop :=
  E.Admits r ∧ ¬ pol r

/-- Write integrity (soundness): every admitted request is authorized by the policy. -/

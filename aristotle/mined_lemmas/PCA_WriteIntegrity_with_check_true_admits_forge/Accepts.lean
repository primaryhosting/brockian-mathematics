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

/-- A write request issued by an actor against a storage target, carrying a
capability token that is supposed to justify the write. -/
structure Write where
  /-- The principal issuing the write. -/
  actor : Nat
  /-- The storage object being written. -/
  target : Nat
  /-- The capability token presented with the write. -/
  token : Nat
deriving DecidableEq, Repr

/-- A write-integrity policy: each target has an owner, and each actor has a
set of valid capability tokens. -/
structure Policy where
  /-- Owner of each target. -/
  owner : Nat → Nat
  /-- Which tokens are valid for a given actor. -/
  validToken : Nat → Nat → Bool

/-- A write is authorized when it is issued by the owner of the target and
carries a token valid for that actor. -/

def Accepts (chk : Check) (w : Write) : Prop := chk w = true

/-- Write-integrity soundness: every accepted write is authorized by the policy. -/

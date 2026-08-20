/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

namespace PCA
namespace WriteIntegrity

/-- A write request submitted to the isolation engine: a principal asks to store
`value` at `key`, presenting the authorization `token` that is supposed to witness
that the write is permitted. -/
structure Write where
  /-- The principal issuing the write. -/
  principal : Nat
  /-- The location being written. -/
  key : Nat
  /-- The value being written. -/
  value : Nat
  /-- The authorization token presented with the request. -/
  token : Nat
  deriving DecidableEq, Repr

/-- The write policy of the isolation engine: which principals may write which
keys, together with the unique token that authorizes each such write. -/
structure Policy where
  /-- `mayWrite p k` holds when principal `p` is permitted to write key `k`. -/
  mayWrite : Nat → Nat → Prop
  /-- `token p k` is the one token that authorizes `p` to write `k`. -/
  token : Nat → Nat → Nat

/-- A write is *authorized* by the policy when the principal is permitted to write
the key **and** presents the matching token. -/

def forgedWrite (P : Policy) : Write :=
  { principal := 0, key := 0, value := 0, token := P.token 0 0 + 1 }

/-- The exhibited request is never authorized: its token differs from the
policy's token for that principal and key. -/

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

/-- Agents (principals) of the isolation engine. -/
abbrev Agent : Type := Nat

/-- Addresses of the guarded store. -/
abbrev Addr : Type := Nat

/-- Values that may be written. -/
abbrev Val : Type := Nat

/-- A write request: a principal asks to put a value at an address. -/
structure Write where
  agent : Agent
  addr : Addr
  val : Val
deriving DecidableEq

/-- A write policy: for each address, the predicate telling which principals are
allowed to write it (the address' ACL). -/
abbrev Policy : Type := Addr → Agent → Prop

/-- A write is *authorized* when its issuing agent lies in the policy's ACL for the
target address. -/

def Authorized (P : Policy) (w : Write) : Prop := P w.addr w.agent

/-- A *check* is the decision procedure the isolation engine runs on each write. -/
abbrev Check : Type := Write → Bool

/-- The engine *admits* a write exactly when its check accepts it. -/

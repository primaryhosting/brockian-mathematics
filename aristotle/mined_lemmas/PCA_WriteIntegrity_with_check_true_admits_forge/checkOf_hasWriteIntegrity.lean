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

theorem checkOf_hasWriteIntegrity (P : Policy) [∀ w : Write, Decidable (Authorized P w)] :
    HasWriteIntegrity P (checkOf P) := by
  intro w hw
  exact of_decide_eq_true hw

/-- **Main result.** If some write `w` is unauthorized under the policy `P`, then the
degenerate check `checkTrue` admits `w`, so `w` is a forge, and consequently `checkTrue`
does not enjoy write integrity for `P`. -/

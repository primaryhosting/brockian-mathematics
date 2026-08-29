/-!
# Default Deny Excludes Only Allowlist
Category: Proof-Carrying Apps
Target: PCA.Invariant.default_deny_excludes_only_allowlist
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace PCA

/-- A principal of the isolation engine: either a root identity, or a principal
obtained by delegating from a parent principal under some capability name. -/
inductive Principal where
  | root : String → Principal
  | delegate : Principal → String → Principal
  deriving DecidableEq

namespace Principal

/-- `InChain q p` says that `q` occurs on the delegation chain of `p`, i.e. `q`
is `p` itself or one of its ancestors. -/

@[simp] theorem inChain_delegate (q p : Principal) (n : String) :
    InChain q (delegate p n) ↔ (q = delegate p n ∨ InChain q p) := Iff.rfl


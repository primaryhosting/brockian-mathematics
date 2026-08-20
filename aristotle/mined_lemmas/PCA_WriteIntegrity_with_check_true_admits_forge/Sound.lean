/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required header comment above is a module docstring, which must be the very
-- first command in the file; Lean therefore forbids any `import` after it. The development
-- below is consequently written against the Lean 4 core library only (no Mathlib lemmas are
-- needed: the goals are closed by `rfl`, `simp` and `omega`, all available in core).

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace PCA.WriteIntegrity

/-- A write request submitted to the isolation engine: it targets a memory `region`,
carries a `payload`, and presents a capability certificate `cert` that is supposed to
witness the writer's authority over that region. -/
structure Write where
  region : Nat
  payload : Nat
  cert : Nat
  deriving DecidableEq

/-- `key r` is the capability token authorizing writes to region `r`.
A write is *authentic* exactly when the certificate it presents is the region's token. -/

def Sound (key : Nat → Nat) (check : Write → Bool) : Prop :=
  ∀ w : Write, Admits check w → Authentic key w

/-- A *forgery* against a checker: a write that the engine admits although it is not
authentic. -/

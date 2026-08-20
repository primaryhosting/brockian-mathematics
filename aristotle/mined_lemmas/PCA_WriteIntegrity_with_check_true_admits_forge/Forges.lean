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

def Forges (key : Nat → Nat) (check : Write → Bool) (w : Write) : Prop :=
  Admits check w ∧ ¬ Authentic key w

/-- **With a trivially-true check, the engine admits a forgery.**

If the isolation engine's write check is the constant `true` predicate, then for *any*
capability assignment `key` there is a write that is admitted yet carries a bogus
certificate; consequently the engine's write-integrity property `Sound` fails.

Interpretation: an always-accepting check discharges no proof obligation, so the
proof-carrying discipline degenerates and write integrity is lost. -/

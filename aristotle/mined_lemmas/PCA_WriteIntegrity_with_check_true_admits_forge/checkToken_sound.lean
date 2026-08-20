/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace PCA.WriteIntegrity

/-- A write request submitted to the isolation engine: a claimed author, a
payload, and an integrity token that is supposed to certify the pair. -/
structure Write where
  author : Nat
  payload : Nat
  token : Nat
  deriving DecidableEq

/-- The integrity token that a genuine author would attach to a write. -/

theorem checkToken_sound : Sound checkToken := by
  intro w hw
  have h : w.token = expected w := of_decide_eq_true hw
  exact h

/-- Soundness and the existence of a forgery are exactly incompatible. -/

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

def checkToken : Write → Bool := fun w => decide (w.token = expected w)

/-- **Main result.** The always-true check admits a forgery, and hence is not a
sound write-integrity policy. -/

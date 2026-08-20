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

def expected (w : Write) : Nat := w.author + w.payload

/-- A write is *authentic* when its token is the one a genuine author would
have produced. -/

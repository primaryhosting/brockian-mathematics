/-!
# With Check True Admits Forge
Category: Proof-Carrying Apps
Target: PCA.WriteIntegrity.with_check_true_admits_forge
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: the required file header is a module doc comment, which Lean requires to come
-- after any `import` lines; to keep the header literally first we develop this file over
-- Lean 4 core only (no imports are needed for the argument below).

namespace PCA
namespace WriteIntegrity

/-- A write request submitted to the isolation engine: the claimed author,
the capability token presented with the request, and the payload. -/
structure Write where
  author : Nat
  token : Nat
  payload : Nat
  deriving DecidableEq

/-- A write is *authorized* (w.r.t. the key assignment `keyOf`) when the presented
token really is the claimed author's capability key. -/

def checkTrue : Engine := fun _ => true

/--
**With check `true`, the engine admits a forgery.**

For every key assignment `keyOf`, the engine that accepts every request admits a write
whose token is not the claimed author's key; consequently that engine is not sound for
write integrity.
-/

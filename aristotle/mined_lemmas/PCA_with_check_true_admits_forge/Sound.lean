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

def Sound (keyOf : Nat → Nat) (e : Engine) : Prop := ∀ w, Admits e w → Authorized keyOf w

/-- The degenerate engine whose check always succeeds. -/

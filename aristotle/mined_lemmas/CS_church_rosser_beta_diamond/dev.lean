/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Trm : Type
  | var : Nat → Trm
  | app : Trm → Trm → Trm
  | lam : Trm → Trm
  deriving DecidableEq

namespace Trm

/-- Lifting of a renaming under a binder. -/

def dev : Trm → Trm
  | .var n => .var n
  | .lam s => .lam (dev s)
  | .app (.lam u) t => Trm.bsubst (dev u) (dev t)
  | .app (.var n) t => .app (.var n) (dev t)
  | .app (.app a b) t => .app (dev (.app a b)) (dev t)


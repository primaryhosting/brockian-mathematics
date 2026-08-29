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

def rn (ξ : Nat → Nat) : Trm → Trm
  | .var n => .var (ξ n)
  | .app s t => .app (rn ξ s) (rn ξ t)
  | .lam s => .lam (rn (upr ξ) s)

/-- Lifting of a substitution under a binder. -/

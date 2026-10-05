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

def sb (σ : Nat → Trm) : Trm → Trm
  | .var n => σ n
  | .app s t => .app (sb σ s) (sb σ t)
  | .lam s => .lam (sb (up σ) s)

/-- Extension of a substitution with a new term for the variable `0`. -/

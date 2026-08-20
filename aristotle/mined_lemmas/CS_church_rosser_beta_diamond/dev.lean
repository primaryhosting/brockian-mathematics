/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Statement: One-step parallel β-reduction in the λ-calculus has the diamond property.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/



namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Term where
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term

namespace Term

/-- Lifting of a renaming under a binder. -/

def dev : Term → Term
  | .var i => .var i
  | .lam s => .lam (dev s)
  | .app (.lam s) t => substOne (dev t) (dev s)
  | .app (.var i) t => .app (.var i) (dev t)
  | .app (.app s₁ s₂) t => .app (dev (.app s₁ s₂)) (dev t)


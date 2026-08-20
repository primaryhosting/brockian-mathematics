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

def rename (r : Nat → Nat) : Term → Term
  | .var i => .var (r i)
  | .app s t => .app (rename r s) (rename r t)
  | .lam s => .lam (rename (upr r) s)

/-- Extending a substitution with a new term at index `0`. -/

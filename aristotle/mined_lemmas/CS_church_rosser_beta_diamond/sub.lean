/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Term : Type
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq

namespace Term

/-- Lift a renaming under a binder. -/

def sub (s : Nat → Term) : Term → Term
  | var n => s n
  | app a b => app (sub s a) (sub s b)
  | lam a => lam (sub (up s) a)

/-- Extend a substitution with a new term for the index `0`. -/

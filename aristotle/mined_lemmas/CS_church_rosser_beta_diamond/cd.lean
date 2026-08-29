/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (This development is self-contained: it needs nothing beyond Lean 4 core.
--  A module docstring header must precede any `import`, so no imports are used.)

set_option autoImplicit false

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Term : Type
  | var : Nat → Term
  | app : Term → Term → Term
  | lam : Term → Term
  deriving DecidableEq, Repr

namespace Term

/-- Lift a renaming under a binder. -/

def cd : Term → Term
  | .var n => .var n
  | .lam t => .lam (cd t)
  | .app (.lam u) t => Term.beta (cd u) (cd t)
  | .app s t => .app (cd s) (cd t)

/-- Takahashi's triangle property: every parallel reduct of `s` parallel-reduces to
the complete development of `s`. -/

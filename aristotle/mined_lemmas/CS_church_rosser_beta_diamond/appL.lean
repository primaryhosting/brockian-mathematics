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

theorem appL {s s' t : Term} (h : Steps s s') : Steps (.app s t) (.app s' t) := by
  induction h with
  | refl => exact .refl _
  | tail _ hst ih => exact .tail ih (.appL hst)


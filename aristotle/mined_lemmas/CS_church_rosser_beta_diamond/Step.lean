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

theorem Step.toPar {s t : Term} (h : Step s t) : Par s t := by
  induction h with
  | beta s t => exact .beta (Par.refl s) (Par.refl t)
  | appL _ ih => exact .app ih (Par.refl _)
  | appR _ ih => exact .app (Par.refl _) ih
  | lam _ ih => exact .lam ih

/-- A parallel reduction step is a finite sequence of ordinary β-steps. -/

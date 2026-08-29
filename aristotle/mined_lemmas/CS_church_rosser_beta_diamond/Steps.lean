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

theorem Steps.toPars {a b : Term} (h : Steps a b) : Pars a b := by
  induction h with
  | refl => exact Pars.refl _
  | tail _ hs ih => exact ih.tail hs.toPar


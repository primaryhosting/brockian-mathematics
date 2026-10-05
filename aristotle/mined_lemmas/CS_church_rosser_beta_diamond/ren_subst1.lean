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

theorem ren_subst1 (r : Nat → Nat) (a b : Term) :
    ren r (subst1 a b) = subst1 (ren (upr r) a) (ren r b) := by
  unfold subst1
  rw [ren_sub, sub_ren]
  congr 1
  funext n
  cases n <;> rfl

/-- A substitution commutes with single substitution. -/

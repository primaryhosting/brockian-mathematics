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

theorem sub_var_id (t : Term) : sub var t = t := by
  induction t with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih =>
      have : up var = var := by funext n; cases n <;> rfl
      simp [this, ih]

/-- Renaming commutes with single substitution. -/

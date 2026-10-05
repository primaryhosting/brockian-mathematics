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

@[simp] theorem cd_app_app (a₁ a₂ b : Term) :
    cd (app (app a₁ a₂) b) = app (cd (app a₁ a₂)) (cd b) := rfl

/-- The key "triangle" property: every parallel reduct of `a` parallel-reduces to the
complete development of `a`. -/

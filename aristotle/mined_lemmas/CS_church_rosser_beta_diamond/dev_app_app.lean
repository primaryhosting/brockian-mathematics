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

@[simp] theorem dev_app_app (s₁ s₂ t : Term) :
    dev (.app (.app s₁ s₂) t) = .app (dev (.app s₁ s₂)) (dev t) := rfl

/-- The triangle property: every parallel reduct of `s` reduces to the complete
development of `s`. -/

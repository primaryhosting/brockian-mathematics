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

theorem rename_rename (r₁ r₂ : Nat → Nat) (t : Term) :
    rename r₁ (rename r₂ t) = rename (r₁ ∘ r₂) t := by
  induction t generalizing r₁ r₂ with
  | var i => rfl
  | app s t ihs iht => simp [ihs, iht]
  | lam s ihs => simp [ihs, upr_comp]


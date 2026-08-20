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

@[simp] theorem up_succ (σ : Nat → Term) (n : Nat) : up σ (n + 1) = rename Nat.succ (σ n) := rfl

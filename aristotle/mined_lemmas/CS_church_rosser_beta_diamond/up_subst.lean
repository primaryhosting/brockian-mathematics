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

theorem up_subst (σ τ : Nat → Term) :
    up (fun n => subst σ (τ n)) = fun n => subst (up σ) (up τ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
      simp [subst_rename, rename_subst]
      rfl


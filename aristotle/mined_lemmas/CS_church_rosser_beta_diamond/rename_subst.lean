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

theorem rename_subst (r : Nat → Nat) (σ : Nat → Term) (t : Term) :
    rename r (subst σ t) = subst (fun n => rename r (σ n)) t := by
  induction t generalizing r σ with
  | var i => rfl
  | app s t ihs iht => simp [ihs, iht]
  | lam s ihs => simp [ihs, up_rename]


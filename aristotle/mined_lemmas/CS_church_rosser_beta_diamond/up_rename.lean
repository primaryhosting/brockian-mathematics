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

theorem up_rename (σ : Nat → Term) (r : Nat → Nat) :
    up (fun n => rename r (σ n)) = fun n => rename (upr r) (up σ n) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [rename_rename]; rfl


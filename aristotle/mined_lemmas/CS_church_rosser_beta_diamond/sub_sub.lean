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

theorem sub_sub (s₁ s₂ : Nat → Term) (t : Term) :
    sub s₂ (sub s₁ t) = sub (fun n => sub s₂ (s₁ n)) t := by
  induction t generalizing s₁ s₂ with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, sub_up]


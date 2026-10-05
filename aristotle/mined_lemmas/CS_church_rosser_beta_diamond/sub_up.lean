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

theorem sub_up (s₁ s₂ : Nat → Term) :
    (fun n => sub (up s₂) (up s₁ n)) = up (fun n => sub s₂ (s₁ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [up, sub_ren, ren_sub]; rfl


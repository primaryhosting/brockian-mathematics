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

theorem sub_ren (s : Nat → Term) (r : Nat → Nat) (t : Term) : sub s (ren r t) = sub (s ∘ r) t := by
  induction t generalizing s r with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, up_comp_upr]


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

theorem ren_up (r : Nat → Nat) (s : Nat → Term) :
    (fun n => ren (upr r) (up s n)) = up (fun n => ren r (s n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [up, ren_ren]; rfl


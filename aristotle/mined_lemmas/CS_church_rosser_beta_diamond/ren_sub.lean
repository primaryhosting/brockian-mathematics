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

theorem ren_sub (r : Nat → Nat) (s : Nat → Term) (t : Term) :
    ren r (sub s t) = sub (fun n => ren r (s n)) t := by
  induction t generalizing r s with
  | var n => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, ren_up]


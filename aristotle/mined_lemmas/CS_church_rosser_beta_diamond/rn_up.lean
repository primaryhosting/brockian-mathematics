/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Trm : Type
  | var : Nat → Trm
  | app : Trm → Trm → Trm
  | lam : Trm → Trm
  deriving DecidableEq

namespace Trm

/-- Lifting of a renaming under a binder. -/

theorem rn_up (ξ : Nat → Nat) (σ : Nat → Trm) :
    (fun n => rn (upr ξ) (up σ n)) = up (fun n => rn ξ (σ n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n => simp [up, rn_rn]; rfl


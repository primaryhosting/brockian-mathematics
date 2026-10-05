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

theorem rn_sb (ξ : Nat → Nat) (σ : Nat → Trm) (t : Trm) :
    rn ξ (sb σ t) = sb (fun n => rn ξ (σ n)) t := by
  induction t generalizing ξ σ with
  | var n => rfl
  | app s t ihs iht => simp [sb, rn, ihs, iht]
  | lam s ih => simp [sb, rn, ih, rn_up]


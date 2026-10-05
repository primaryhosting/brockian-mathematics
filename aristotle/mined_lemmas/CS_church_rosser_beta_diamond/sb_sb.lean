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

theorem sb_sb (σ τ : Nat → Trm) (t : Trm) :
    sb σ (sb τ t) = sb (fun n => sb σ (τ n)) t := by
  induction t generalizing σ τ with
  | var n => rfl
  | app s t ihs iht => simp [sb, ihs, iht]
  | lam s ih => simp [sb, ih, sb_up]


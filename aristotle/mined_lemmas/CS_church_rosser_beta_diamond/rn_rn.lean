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

theorem rn_rn (ζ ξ : Nat → Nat) (t : Trm) : rn ζ (rn ξ t) = rn (ζ ∘ ξ) t := by
  induction t generalizing ζ ξ with
  | var n => rfl
  | app s t ihs iht => simp [rn, ihs, iht]
  | lam s ih => simp [rn, ih, upr_comp]


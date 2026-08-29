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

theorem rn_bsubst (ξ : Nat → Nat) (s u : Trm) :
    rn ξ (bsubst s u) = bsubst (rn (upr ξ) s) (rn ξ u) := by
  unfold bsubst
  rw [rn_sb, sb_rn]
  congr 1
  funext n
  cases n <;> rfl

/-- Substitution composed with β-substitution. -/

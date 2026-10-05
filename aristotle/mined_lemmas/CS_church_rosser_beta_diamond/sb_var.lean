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

theorem sb_var (t : Trm) : sb Trm.var t = t := by
  induction t with
  | var n => rfl
  | app s t ihs iht => simp [sb, ihs, iht]
  | lam s ih =>
      have h : up Trm.var = Trm.var := by funext n; cases n <;> rfl
      simp [sb, h, ih]

/-- Renaming commutes with β-substitution. -/

/-!
# Church Rosser Beta Diamond
Category: Computer Science
Target: CS.church_rosser_beta_diamond
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CS

/-- Untyped λ-terms in de Bruijn representation. -/
inductive Trm : Type
  | var : Nat → Trm
  | app : Trm → Trm → Trm
  | lam : Trm → Trm
  deriving DecidableEq

namespace Trm

/-- Lifting a renaming under a binder. -/

theorem betas_confluent {a b c : Trm} (hab : Betas a b) (hac : Betas a c) :
    ∃ d : Trm, Betas b d ∧ Betas c d := by
  obtain ⟨d, hbd, hcd⟩ := pars_confluent hab.pars hac.pars
  exact ⟨d, hbd.betas, hcd.betas⟩

end Trm

/-- **Diamond property for parallel β-reduction.**  If a λ-term `t` parallel-β-reduces
in one step to both `u` and `v`, then `u` and `v` have a common parallel-β-reduct. -/

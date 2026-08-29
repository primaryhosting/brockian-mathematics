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

theorem pars_confluent {a b c : Trm} (hab : Pars a b) (hac : Pars a c) :
    ∃ d : Trm, Pars b d ∧ Pars c d := by
  induction hab with
  | refl => exact ⟨c, hac, Pars.refl c⟩
  | @tail x b _ hxb ih =>
    obtain ⟨d, hxd, hcd⟩ := ih
    obtain ⟨e, hbe, hde⟩ := par_pars_strip hxb hxd
    exact ⟨e, hbe, hcd.trans ((Pars.refl d).tail hde)⟩

/-- **Church-Rosser theorem for β-reduction**: β-reduction is confluent. -/

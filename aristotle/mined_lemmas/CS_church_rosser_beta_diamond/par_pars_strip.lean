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

theorem par_pars_strip {a b c : Trm} (hab : Par a b) (hac : Pars a c) :
    ∃ d : Trm, Pars b d ∧ Par c d := by
  induction hac with
  | refl => exact ⟨b, Pars.refl b, hab⟩
  | @tail x y _ hxy ih =>
    obtain ⟨d, hbd, hxd⟩ := ih
    exact ⟨star x, hbd.tail (par_star hxd), par_star hxy⟩

/-- Confluence of parallel β-reduction sequences. -/

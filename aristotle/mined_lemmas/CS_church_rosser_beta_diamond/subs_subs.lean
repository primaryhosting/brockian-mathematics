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

theorem subs_subs (t : Trm) (s s' : Nat → Trm) :
    subs s (subs s' t) = subs (fun n => subs s (s' n)) t := by
  induction t generalizing s s' with
  | var i => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih => simp [ih, up_subs]


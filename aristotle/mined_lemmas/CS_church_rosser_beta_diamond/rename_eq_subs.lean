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

theorem rename_eq_subs (t : Trm) (r : Nat → Nat) : rename r t = subs (fun n => var (r n)) t := by
  induction t generalizing r with
  | var i => rfl
  | app a b iha ihb => simp [iha, ihb]
  | lam a ih =>
    have h : (fun n => var (upr r n)) = up (fun n => var (r n)) := by
      funext n; cases n <;> rfl
    simp [ih, h]


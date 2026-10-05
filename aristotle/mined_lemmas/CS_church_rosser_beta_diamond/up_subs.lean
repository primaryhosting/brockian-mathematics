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

theorem up_subs (s s' : Nat → Trm) :
    (fun n => subs (up s) (up s' n)) = up (fun n => subs s (s' n)) := by
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show subs (up s) (rename Nat.succ (s' n)) = rename Nat.succ (subs s (s' n))
    rw [subs_rename, rename_subs]
    rfl


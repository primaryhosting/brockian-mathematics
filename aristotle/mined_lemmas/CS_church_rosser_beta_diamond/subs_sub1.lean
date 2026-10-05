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

theorem subs_sub1 (a b : Trm) (s : Nat → Trm) :
    subs s (sub1 a b) = sub1 (subs (up s) a) (subs s b) := by
  unfold sub1
  rw [subs_subs, subs_subs]
  congr 1
  funext n
  cases n with
  | zero => rfl
  | succ n =>
    show s n = subs (cons (subs s b)) (rename Nat.succ (s n))
    rw [subs_rename]
    exact (subs_id _).symm


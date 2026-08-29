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

theorem rename_sub1 (a b : Trm) (r : Nat → Nat) :
    rename r (sub1 a b) = sub1 (rename (upr r) a) (rename r b) := by
  rw [rename_eq_subs, subs_sub1, rename_eq_subs a, rename_eq_subs b]
  congr 2
  funext n; cases n <;> rfl

/-! ### Parallel β-reduction -/

/-- One-step parallel β-reduction. -/
inductive Par : Trm → Trm → Prop
  | var (i : Nat) : Par (var i) (var i)
  | lam {a a' : Trm} : Par a a' → Par (lam a) (lam a')
  | app {a a' b b' : Trm} : Par a a' → Par b b' → Par (app a b) (app a' b')
  | beta {a a' b b' : Trm} : Par a a' → Par b b' → Par (app (lam a) b) (sub1 a' b')


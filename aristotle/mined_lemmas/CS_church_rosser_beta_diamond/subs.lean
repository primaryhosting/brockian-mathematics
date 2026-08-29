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

def subs : (Nat → Trm) → Trm → Trm
  | s, var i => s i
  | s, app a b => app (subs s a) (subs s b)
  | s, lam a => lam (subs (up s) a)

/-- The substitution sending `0` to `b` and `n+1` to `n`. -/

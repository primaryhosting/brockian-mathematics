import Mathlib
import RequestProject.Main

/-!
# Mathlib-flavoured corollary of `with_check_true_admits_forge`

`RequestProject/Main.lean` must begin with a mandated module doc comment, which
forces that module to be import-free (Lean rejects `import` after a doc comment).
This companion module imports Mathlib and restates the main result in terms of
the *set* of admitted forgeries.
-/

set_option autoImplicit false

namespace PCA
namespace WriteIntegrity

/-- The set of requests that the engine admits even though they are forged. -/

theorem admits_of_check_true
    (E : Engine) (hE : ∀ r : Request, E.check r = true) (r : Request) :
    Admits E r := hE r

/-- **With a constant-`true` check, the engine admits a forgery.**

If the isolation engine's write guard is the constant `true` predicate, then for
any policy that actually forbids something (some principal is unauthorized for
some location) the engine admits a forged write, and consequently it does not
enforce write integrity. -/

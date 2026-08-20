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

def admittedForgeries (E : Engine) (auth : Policy) : Set Request :=
  {r | Admits E r ∧ Forged auth r}

/-- With a constant-`true` guard the set of admitted forgeries is nonempty
(whenever the policy forbids something), so write integrity fails. -/

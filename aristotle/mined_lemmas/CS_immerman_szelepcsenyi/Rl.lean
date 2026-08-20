import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS


def Rl (r : Fin m → Fin m → Lit n) (x : Fin n → Bool) (u v : Fin m) : Prop :=
  (r u v).holds x

/-- `RS r s x i v` says that `v` is reachable from `s` in at most `i` steps. -/

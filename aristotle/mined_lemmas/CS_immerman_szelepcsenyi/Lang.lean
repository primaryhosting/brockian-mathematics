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


def Lang : Type := (n : ℕ) → (Fin n → Bool) → Prop

/-- The class of languages recognised by nondeterministic machines with polynomially
many configurations, that is, nondeterministic logarithmic space. -/

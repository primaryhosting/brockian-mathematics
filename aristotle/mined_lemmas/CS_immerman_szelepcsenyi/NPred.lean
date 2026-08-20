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


def NPred (I : ℕ) (v : Fin m) : Fin m → Prop :=
  fun u => RS r s x I u ∧ ¬(u = v ∨ Rl r x u v)

/-- The invariant of the counting machine. -/

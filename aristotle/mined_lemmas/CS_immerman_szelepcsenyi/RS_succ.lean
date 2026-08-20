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


lemma RS_succ (i : ℕ) (v : Fin m) :
    RS r s x (i + 1) v ↔ ∃ u, RS r s x i u ∧ (u = v ∨ Rl r x u v) := Iff.rfl


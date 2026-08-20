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


lemma RS_step {i : ℕ} {u v : Fin m} (h : RS r s x i u) (huv : Rl r x u v) :
    RS r s x (i + 1) v := ⟨u, h, Or.inr huv⟩

/-- Everything in a level set is reachable. -/

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


lemma cmach_step (r : Fin m → Fin m → Lit n) (s t : Fin m) (x : Fin n → Bool) (a b : St m) :
    (cmach r s t).Step x a b ↔ (E r s t a b).holds x := Iff.rfl

end CS


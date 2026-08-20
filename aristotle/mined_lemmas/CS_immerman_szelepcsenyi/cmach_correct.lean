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


theorem cmach_correct (r : Fin m → Fin m → Lit n) (s t : Fin m) (x : Fin n → Bool) :
    (cmach r s t).Accepts x ↔ ¬ Relation.ReflTransGen (Rl r x) s t :=
  ⟨cmach_sound r s t x, cmach_complete r s t x⟩

/-- The machine complementing `M`: the counting machine run on the configuration graph
of `M`, transported to `Fin (Fintype.card M.V)`. -/

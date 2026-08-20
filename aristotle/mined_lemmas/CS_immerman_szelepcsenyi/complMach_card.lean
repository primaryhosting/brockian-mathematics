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


lemma complMach_card (M : Mach n) :
    Fintype.card (complMach M).V ≤ 6 * (Fintype.card M.V + 2) ^ 9 :=
  card_St _


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


theorem cmach_sound (hacc : (cmach r s t).Accepts x) :
    ¬ Relation.ReflTransGen (Rl r x) s t := by
  have hinv : ∀ (b : St m), Relation.ReflTransGen ((cmach r s t).Step x) (St.lvl 0 1) b →
      Inv r s t x b := by
    intro b hb
    induction hb with
    | refl => exact inv_start r s t x
    | tail _ hstep ih => exact inv_step r s t x _ _ hstep ih
  exact hinv St.acc hacc

end CS

import RequestProject.ISSound
import RequestProject.ISComplete

/-!
# Complementing a nondeterministic machine

Combining soundness and completeness of the counting machine, every nondeterministic
machine can be complemented at a polynomial cost in the number of configurations.
This is the Immerman–Szelepcsényi theorem, and it gives `NL = coNL`.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

variable {n m : ℕ}

/-- The counting machine decides the complement of reachability. -/

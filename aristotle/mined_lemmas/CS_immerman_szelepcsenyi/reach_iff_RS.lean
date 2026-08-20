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


lemma reach_iff_RS (t : Fin m) :
    Relation.ReflTransGen (Rl r x) s t ↔ RS r s x (m + 1) t := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := reach_RS r s x h
    exact RS_stab r s x i hi
  · intro h; exact RS_reach r s x h

end CS

import RequestProject.ISMachine

/-!
# Soundness of the counting machine

We exhibit an invariant of the counting machine which holds at the initial configuration,
is preserved by every transition, and which at the accepting configuration says that `t`
is not reachable from `s`.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

variable {n m : ℕ} (r : Fin m → Fin m → Lit n) (s t : Fin m) (x : Fin n → Bool)

/-- The invariant attached to the loop over vertices: `c` is the exact number of vertices
of level `i`, and `c'` is the exact number of vertices of level `i+1` among the first `j`
vertices. -/

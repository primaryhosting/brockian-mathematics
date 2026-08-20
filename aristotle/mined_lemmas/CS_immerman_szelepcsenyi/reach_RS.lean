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


lemma reach_RS {v : Fin m} (h : Relation.ReflTransGen (Rl r x) s v) :
    ∃ i, RS r s x i v := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
      obtain ⟨i, hi⟩ := ih
      exact ⟨i + 1, RS_step r s x hi hstep⟩

/-- The level sets, as sets. -/

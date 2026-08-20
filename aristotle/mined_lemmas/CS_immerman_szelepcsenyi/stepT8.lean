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


lemma stepT8 (i c j c' jj d k k2 : Fin (m + 2)) (v u w : Fin m)
    (hk2 : (k2 : ℕ) = (k : ℕ) + 1) (huw : u = w ∨ Rl r x u w) :
    (cmach r s t).Step x (St.walkN i c j c' v jj d u k) (St.walkN i c j c' v jj d w k2) := by
  show (E r s t (St.walkN i c j c' v jj d u k) (St.walkN i c j c' v jj d w k2)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, hk2⟩]
  by_cases hwu : w = u
  · rw [if_pos hwu]; trivial
  · rw [if_neg hwu]
    rcases huw with rfl | hs
    · exact absurd rfl hwu
    · exact hs


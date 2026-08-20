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


lemma stepT11 (i c j c' i2 : Fin (m + 2)) (hj : (j : ℕ) = m) (hi2 : (i2 : ℕ) = (i : ℕ) + 1) :
    (cmach r s t).Step x (St.outer i c j c') (St.lvl i2 c') := by
  show (E r s t (St.outer i c j c') (St.lvl i2 c')).holds x
  simp only [E]
  rw [if_pos ⟨hj, hi2, trivial⟩]
  trivial


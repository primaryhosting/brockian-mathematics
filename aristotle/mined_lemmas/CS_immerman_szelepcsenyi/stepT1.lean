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


lemma stepT1 (i c j c' : Fin (m + 2)) (hj : (j : ℕ) = 0) (hc' : (c' : ℕ) = 0) :
    (cmach r s t).Step x (St.lvl i c) (St.outer i c j c') := by
  show (E r s t (St.lvl i c) (St.outer i c j c')).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, hj, hc'⟩]
  trivial


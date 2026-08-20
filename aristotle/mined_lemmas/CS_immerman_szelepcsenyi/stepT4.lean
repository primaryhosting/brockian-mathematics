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


lemma stepT4 (i c j c' j2 c2' k : Fin (m + 2)) (w : Fin m) (hk : (k : ℕ) = (i : ℕ) + 1)
    (hw : (w : ℕ) = (j : ℕ)) (hj2 : (j2 : ℕ) = (j : ℕ) + 1)
    (hc2' : (c2' : ℕ) = (c' : ℕ) + 1) :
    (cmach r s t).Step x (St.walkY i c j c' w k) (St.outer i c j2 c2') := by
  show (E r s t (St.walkY i c j c' w k) (St.outer i c j2 c2')).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, hk, hw, hj2, hc2'⟩]
  trivial


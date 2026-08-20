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


lemma stepT7 (i c j c' jj d k : Fin (m + 2)) (v : Fin m) (hk : (k : ℕ) = 0)
    (hjm : (jj : ℕ) < m) :
    (cmach r s t).Step x (St.no i c j c' v jj d) (St.walkN i c j c' v jj d s k) := by
  show (E r s t (St.no i c j c' v jj d) (St.walkN i c j c' v jj d s k)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, hk, hjm⟩]
  trivial


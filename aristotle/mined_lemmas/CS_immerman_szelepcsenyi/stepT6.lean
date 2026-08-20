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


lemma stepT6 (i c j c' jj jj2 d : Fin (m + 2)) (v : Fin m)
    (hjj2 : (jj2 : ℕ) = (jj : ℕ) + 1) (hjm : (jj : ℕ) < m) :
    (cmach r s t).Step x (St.no i c j c' v jj d) (St.no i c j c' v jj2 d) := by
  show (E r s t (St.no i c j c' v jj d) (St.no i c j c' v jj2 d)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, trivial, trivial, hjj2, hjm⟩]
  trivial


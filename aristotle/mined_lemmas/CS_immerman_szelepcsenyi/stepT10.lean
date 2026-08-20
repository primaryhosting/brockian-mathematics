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


lemma stepT10 (i c j c' jj d j2 : Fin (m + 2)) (v : Fin m) (hjj : (jj : ℕ) = m) (hd : d = c)
    (hv : (v : ℕ) = (j : ℕ)) (hj2 : (j2 : ℕ) = (j : ℕ) + 1) :
    (cmach r s t).Step x (St.no i c j c' v jj d) (St.outer i c j2 c') := by
  show (E r s t (St.no i c j c' v jj d) (St.outer i c j2 c')).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, hjj, hd, hv, hj2⟩]
  trivial


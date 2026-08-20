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


lemma stepT5 (i c j c' jj d : Fin (m + 2)) (v : Fin m) (hv : (v : ℕ) = (j : ℕ))
    (hjm : (j : ℕ) < m) (hjj : (jj : ℕ) = 0) (hd : (d : ℕ) = 0) :
    (cmach r s t).Step x (St.outer i c j c') (St.no i c j c' v jj d) := by
  show (E r s t (St.outer i c j c') (St.no i c j c' v jj d)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, hv, hjm, hjj, hd⟩]
  trivial


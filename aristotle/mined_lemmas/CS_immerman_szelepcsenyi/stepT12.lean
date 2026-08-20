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


lemma stepT12 (i c j c' jj d : Fin (m + 2)) (hi : (i : ℕ) = m) (hjj : (jj : ℕ) = m)
    (hd : d = c) :
    (cmach r s t).Step x (St.no i c j c' t jj d) St.acc := by
  show (E r s t (St.no i c j c' t jj d) St.acc).holds x
  simp only [E]
  rw [if_pos ⟨hi, hjj, hd, trivial⟩]
  trivial

/-! ### Walks -/

/-- A vertex of level `K` can be reached by a walk of exactly `K` steps. -/

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


lemma stepT9 (i c j c' jj jj2 d d2 k : Fin (m + 2)) (v w : Fin m)
    (hk : (k : ℕ) = (i : ℕ)) (hw : (w : ℕ) = (jj : ℕ)) (hjj2 : (jj2 : ℕ) = (jj : ℕ) + 1)
    (hd2 : (d2 : ℕ) = (d : ℕ) + 1) (hwv : w ≠ v) (hnr : ¬ Rl r x w v) :
    (cmach r s t).Step x (St.walkN i c j c' v jj d w k) (St.no i c j c' v jj2 d2) := by
  show (E r s t (St.walkN i c j c' v jj d w k) (St.no i c j c' v jj2 d2)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, trivial, hk, hw, hjj2, hd2⟩, if_neg hwv]
  exact (Lit.holds_neg x (r w v)).mpr hnr


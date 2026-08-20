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


lemma cntb_succ_not (P : Fin m → Prop) (J : ℕ) (w : Fin m) (hw : ¬ P w) (hJ : (w : ℕ) = J) :
    cntb P (J + 1) = cntb P J := by
  have hset : {v : Fin m | P v ∧ (v : ℕ) < J + 1} = {v : Fin m | P v ∧ (v : ℕ) < J} := by
    ext u
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hP, hlt⟩
      refine ⟨hP, ?_⟩
      rcases Nat.lt_or_ge (u : ℕ) J with h | h
      · exact h
      · exact absurd (show P w from (Fin.ext (show (u:ℕ) = (w:ℕ) by omega) : u = w) ▸ hP) hw
    · rintro ⟨hP, hlt⟩; exact ⟨hP, by omega⟩
  simp only [cntb, cnt, hset]


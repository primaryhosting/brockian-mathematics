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


lemma cntb_succ_mem (P : Fin m → Prop) (J : ℕ) (w : Fin m) (hw : P w) (hJ : (w : ℕ) = J) :
    cntb P (J + 1) = cntb P J + 1 := by
  have hset : {v : Fin m | P v ∧ (v : ℕ) < J + 1} = insert w {v : Fin m | P v ∧ (v : ℕ) < J} := by
    ext u
    simp only [Set.mem_insert_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hP, hlt⟩
      rcases Nat.lt_or_ge (u : ℕ) J with h | h
      · exact Or.inr ⟨hP, h⟩
      · exact Or.inl (Fin.ext (by omega))
    · rintro (rfl | ⟨hP, hlt⟩)
      · exact ⟨hw, by omega⟩
      · exact ⟨hP, by omega⟩
  have hnot : w ∉ {v : Fin m | P v ∧ (v : ℕ) < J} := by simp [hJ]
  simp only [cntb, cnt, hset]
  exact Set.ncard_insert_of_notMem hnot (Set.toFinite _)


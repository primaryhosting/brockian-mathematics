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


lemma level_loop :
    ∀ (I : ℕ), I ≤ m → ∀ (jf cf : Fin (m + 2)), (jf : ℕ) = I →
      (cf : ℕ) = cnt (RS r s x I) →
      Relation.ReflTransGen ((cmach r s t).Step x) (St.lvl 0 1) (St.lvl jf cf) := by
  intro I
  induction I with
  | zero =>
      intro _ jf cf hjf hcf
      have h1 : jf = 0 := Fin.ext (by rw [hjf, val_zero'])
      have hset : {v : Fin m | RS r s x 0 v} = {s} := by
        ext v; simp [RS_zero]
      have h2 : cf = 1 :=
        Fin.ext (by rw [hcf, cnt, hset, Set.ncard_singleton, val_one'])
      rw [h1, h2]
  | succ I ih =>
      intro hI jf cf hjf hcf
      have hIlt : I < m + 2 := by omega
      have hcI : cnt (RS r s x I) ≤ m := cnt_le _
      obtain ⟨if0, hif0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = I := ⟨⟨I, hIlt⟩, rfl⟩
      obtain ⟨cf0, hcf0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = cnt (RS r s x I) :=
        ⟨⟨cnt (RS r s x I), by omega⟩, rfl⟩
      obtain ⟨jm, hjm⟩ : ∃ f : Fin (m + 2), (f : ℕ) = m := ⟨⟨m, by omega⟩, rfl⟩
      have hpath := ih (by omega) if0 cf0 hif0 hcf0
      have hstart := hpath.tail (stepT1 r s t x if0 cf0 0 0 (val_zero' m) (val_zero' m))
      have hloop := outer_loop r s t x if0 cf0 (by rw [hif0]; omega) (by rw [hcf0, hif0])
        m le_rfl jm cf hjm
        (by rw [hcf, hif0, cntb_full])
      exact (hstart.trans hloop).tail
        (stepT11 r s t x if0 cf0 jm cf jf hjm (by rw [hjf, hif0]))

/-! ### Completeness -/

/-- If `t` is not reachable from `s`, the counting machine accepts. -/

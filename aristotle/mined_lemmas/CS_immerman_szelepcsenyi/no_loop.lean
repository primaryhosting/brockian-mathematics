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


lemma no_loop (i c j c' : Fin (m + 2)) (v : Fin m) (hv : ¬ RS r s x ((i : ℕ) + 1) v) :
    ∀ (J : ℕ), J ≤ m → ∀ (jf df : Fin (m + 2)), (jf : ℕ) = J →
      (df : ℕ) = cntb (RS r s x (i : ℕ)) J →
      Relation.ReflTransGen ((cmach r s t).Step x)
        (St.no i c j c' v 0 0) (St.no i c j c' v jf df) := by
  intro J
  induction J with
  | zero =>
      intro _ jf df hjf hdf
      have h1 : jf = 0 := Fin.ext (by rw [hjf, val_zero'])
      have h2 : df = 0 := Fin.ext (by rw [hdf, cntb_zero, val_zero'])
      rw [h1, h2]
  | succ J ih =>
      intro hJ jf df hjf hdf
      have hJm : J < m := by omega
      have hJlt : J < m + 2 := by omega
      have hilt : (i : ℕ) < m + 2 := i.isLt
      have hcJ : cntb (RS r s x (i : ℕ)) J ≤ m := cntb_le _ _
      obtain ⟨u, hu⟩ : ∃ u : Fin m, (u : ℕ) = J := ⟨⟨J, hJm⟩, rfl⟩
      obtain ⟨jf0, hjf0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = J := ⟨⟨J, hJlt⟩, rfl⟩
      obtain ⟨df0, hdf0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = cntb (RS r s x (i : ℕ)) J :=
        ⟨⟨cntb (RS r s x (i : ℕ)) J, by omega⟩, rfl⟩
      have hpath := ih (by omega) jf0 df0 hjf0 hdf0
      by_cases hmem : RS r s x (i : ℕ) u
      · -- certify that `u` belongs to level `i`, and count it
        have hwv : u ≠ v := fun h => hv ⟨u, hmem, Or.inl h⟩
        have hnrl : ¬ Rl r x u v := fun h => hv ⟨u, hmem, Or.inr h⟩
        obtain ⟨kf, hkf⟩ : ∃ f : Fin (m + 2), (f : ℕ) = (i : ℕ) := ⟨⟨(i : ℕ), by omega⟩, rfl⟩
        have hstart := hpath.tail
          (stepT7 r s t x i c j c' jf0 df0 0 v (val_zero' m) (by rw [hjf0]; exact hJm))
        have hwalk := walkN_reach r s t x i c j c' jf0 df0 v (i : ℕ) u kf hkf hmem
        refine (hstart.trans hwalk).tail ?_
        refine stepT9 r s t x i c j c' jf0 jf df0 df kf v u hkf (by rw [hu, hjf0])
          (by rw [hjf, hjf0]) ?_ hwv hnrl
        rw [hdf, hdf0]
        exact cntb_succ_mem _ _ u hmem hu
      · -- skip `u`
        have hdfeq : df = df0 :=
          Fin.ext (by rw [hdf, hdf0]; exact cntb_succ_not _ _ u hmem hu)
        rw [hdfeq]
        exact hpath.tail
          (stepT6 r s t x i c j c' jf0 jf df0 v (by rw [hjf, hjf0]) (by rw [hjf0]; exact hJm))

/-! ### The outer loop: computing the size of level `i+1` -/


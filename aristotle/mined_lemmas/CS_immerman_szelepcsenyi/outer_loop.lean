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


lemma outer_loop (i c : Fin (m + 2)) (hi : (i : ℕ) ≤ m)
    (hc : (c : ℕ) = cnt (RS r s x (i : ℕ))) :
    ∀ (J : ℕ), J ≤ m → ∀ (jf cf : Fin (m + 2)), (jf : ℕ) = J →
      (cf : ℕ) = cntb (RS r s x ((i : ℕ) + 1)) J →
      Relation.ReflTransGen ((cmach r s t).Step x)
        (St.outer i c 0 0) (St.outer i c jf cf) := by
  intro J
  induction J with
  | zero =>
      intro _ jf cf hjf hcf
      have h1 : jf = 0 := Fin.ext (by rw [hjf, val_zero'])
      have h2 : cf = 0 := Fin.ext (by rw [hcf, cntb_zero, val_zero'])
      rw [h1, h2]
  | succ J ih =>
      intro hJ jf cf hjf hcf
      have hJm : J < m := by omega
      have hJlt : J < m + 2 := by omega
      have hilt : (i : ℕ) < m + 2 := i.isLt
      have hcJ : cntb (RS r s x ((i : ℕ) + 1)) J ≤ m := cntb_le _ _
      obtain ⟨v, hvJ⟩ : ∃ v : Fin m, (v : ℕ) = J := ⟨⟨J, hJm⟩, rfl⟩
      obtain ⟨jf0, hjf0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = J := ⟨⟨J, hJlt⟩, rfl⟩
      obtain ⟨cf0, hcf0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = cntb (RS r s x ((i : ℕ) + 1)) J :=
        ⟨⟨cntb (RS r s x ((i : ℕ) + 1)) J, by omega⟩, rfl⟩
      have hpath := ih (by omega) jf0 cf0 hjf0 hcf0
      by_cases hmem : RS r s x ((i : ℕ) + 1) v
      · -- guess that `v` belongs to level `i+1` and certify it by a walk
        obtain ⟨kf, hkf⟩ : ∃ f : Fin (m + 2), (f : ℕ) = (i : ℕ) + 1 :=
          ⟨⟨(i : ℕ) + 1, by omega⟩, rfl⟩
        have hstart := hpath.tail
          (stepT2 r s t x i c jf0 cf0 0 (val_zero' m) (by rw [hjf0]; exact hJm))
        have hwalk := walkY_reach r s t x i c jf0 cf0 ((i : ℕ) + 1) v kf hkf hmem
        refine (hstart.trans hwalk).tail ?_
        refine stepT4 r s t x i c jf0 cf0 jf cf kf v hkf (by rw [hvJ, hjf0])
          (by rw [hjf, hjf0]) ?_
        rw [hcf, hcf0]
        exact cntb_succ_mem _ _ v hmem hvJ
      · -- guess that `v` does not belong to level `i+1` and run the inner loop
        have hcfeq : cf = cf0 :=
          Fin.ext (by rw [hcf, hcf0]; exact cntb_succ_not _ _ v hmem hvJ)
        obtain ⟨jm, hjm⟩ : ∃ f : Fin (m + 2), (f : ℕ) = m := ⟨⟨m, by omega⟩, rfl⟩
        have hstart := hpath.tail
          (stepT5 r s t x i c jf0 cf0 0 0 v (by rw [hvJ, hjf0]) (by rw [hjf0]; exact hJm)
            (val_zero' m) (val_zero' m))
        have hloop := no_loop r s t x i c jf0 cf0 v hmem m le_rfl jm c hjm
          (by rw [hc, cntb_full])
        rw [hcfeq]
        exact (hstart.trans hloop).tail
          (stepT10 r s t x i c jf0 cf0 jm c jf v hjm rfl (by rw [hvJ, hjf0])
            (by rw [hjf, hjf0]))

/-! ### The outermost loop: going through the levels -/


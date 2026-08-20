/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (it uses only the Lean 4 core library), so that the
required header comment above can literally be the first thing in the file.
-/

namespace CS

/-! ## Counting -/

/-- `HasCard α N` says that the type `α` embeds into `Fin N`; i.e. `α` has at most `N`
elements, so an element of `α` can be stored in `⌈log₂ N⌉` bits. -/

theorem run_invariant {n d : Nat} (G : RotGraph n d) (D : Nat) (hd : 0 < d) (s t : Fin n) :
    ∀ j : Nat, j ≤ Tm d D →
      ((iterate ((ustconMachine n d D hd).step G) j
          ((ustconMachine n d D hd).init s t) : memT n d D).1 = s ∧
       (iterate ((ustconMachine n d D hd).step G) j
          ((ustconMachine n d D hd).init s t) : memT n d D).2.1 = t ∧
       (iterate ((ustconMachine n d D hd).step G) j
          ((ustconMachine n d D hd).init s t) : memT n d D).2.2.1.1 = j ∧
       (iterate ((ustconMachine n d D hd).step G) j
          ((ustconMachine n d D hd).init s t) : memT n d D).2.2.2.1 = vAt G D hd s j ∧
       ((iterate ((ustconMachine n d D hd).step G) j
          ((ustconMachine n d D hd).init s t) : memT n d D).2.2.2.2 = true ↔
          ∃ k, k ≤ j ∧ vAt G D hd s k = t)) := by
  intro j
  induction j with
  | zero =>
      intro _
      refine ⟨rfl, rfl, rfl, rfl, ?_⟩
      show (decide (s = t) = true) ↔ _
      constructor
      · intro h
        exact ⟨0, Nat.le_refl _, by rw [vAt_zero]; exact of_decide_eq_true h⟩
      · rintro ⟨k, hk, hkt⟩
        have hk0 : k = 0 := Nat.le_zero.mp hk
        subst hk0
        rw [vAt_zero] at hkt
        simp [hkt]
  | succ j ih =>
      intro hj
      have hj' : j ≤ Tm d D := Nat.le_of_succ_le hj
      obtain ⟨h1, h2, h3, h4, h5⟩ := ih hj'
      set m : memT n d D := iterate ((ustconMachine n d D hd).step G) j
        ((ustconMachine n d D hd).init s t) with hm
      have hstep : (iterate ((ustconMachine n d D hd).step G) (j + 1)
          ((ustconMachine n d D hd).init s t) : memT n d D)
          = upd D m (G.rot (qry D hd m)) := rfl
      have hjval : min (j + 1) (Tm d D) = j + 1 := by omega
      by_cases hcase : j % (D + 1) = D
      · have hupd : upd D m (G.rot (qry D hd m))
            = (m.1, m.2.1, (⟨min (j + 1) (Tm d D), by omega⟩ : Fin (Tm d D + 1)),
                m.1, m.2.2.2.2) := by
          show (if m.2.2.1.1 % (D + 1) = D then _ else _) = _
          rw [h3]
          simp [hcase]
        rw [hstep, hupd]
        refine ⟨h1, h2, by simpa using hjval, ?_, ?_⟩
        · show m.1 = vAt G D hd s (j + 1)
          rw [h1, vAt_reset G D hd s hcase]
        · show m.2.2.2.2 = true ↔ _
          rw [h5]
          constructor
          · rintro ⟨k, hk, hkt⟩; exact ⟨k, by omega, hkt⟩
          · rintro ⟨k, hk, hkt⟩
            rcases Nat.lt_or_ge k (j + 1) with hlt | hge
            · exact ⟨k, by omega, hkt⟩
            · have hkj : k = j + 1 := by omega
              subst hkj
              rw [vAt_reset G D hd s hcase] at hkt
              exact ⟨0, Nat.zero_le _, by rw [vAt_zero]; exact hkt⟩
      · have hq : qry D hd m = (vAt G D hd s j, digitF hd (j / (D + 1)) (j % (D + 1))) := by
          show (m.2.2.2.1, digitF hd (m.2.2.1.1 / (D + 1)) (m.2.2.1.1 % (D + 1))) = _
          rw [h3, h4]
        have hnext : (G.rot (qry D hd m)).1 = vAt G D hd s (j + 1) := by
          rw [hq, vAt_advance G D hd s hcase]
          rfl
        have hupd : upd D m (G.rot (qry D hd m))
            = (m.1, m.2.1, (⟨min (j + 1) (Tm d D), by omega⟩ : Fin (Tm d D + 1)),
                (G.rot (qry D hd m)).1,
                m.2.2.2.2 || decide ((G.rot (qry D hd m)).1 = m.2.1)) := by
          show (if m.2.2.1.1 % (D + 1) = D then _ else _) = _
          rw [h3]
          simp [hcase]
        rw [hstep, hupd]
        refine ⟨h1, h2, by simpa using hjval, hnext, ?_⟩
        show (m.2.2.2.2 || decide ((G.rot (qry D hd m)).1 = m.2.1)) = true ↔ _
        rw [h2, hnext]
        constructor
        · intro h
          rcases Bool.or_eq_true_iff.mp h with hA | hB
          · obtain ⟨k, hk, hkt⟩ := h5.mp hA
            exact ⟨k, by omega, hkt⟩
          · exact ⟨j + 1, Nat.le_refl _, of_decide_eq_true hB⟩
        · rintro ⟨k, hk, hkt⟩
          rcases Nat.lt_or_ge k (j + 1) with hlt | hge
          · have hA : m.2.2.2.2 = true := h5.mpr ⟨k, by omega, hkt⟩
            rw [hA]; rfl
          · have hkj : k = j + 1 := by omega
            subst hkj
            rw [decide_eq_true hkt]
            exact Bool.or_true _

/-- Correctness of the enumeration: the algorithm visits `t` iff there is a walk of length
at most `D` from `s` to `t`. -/

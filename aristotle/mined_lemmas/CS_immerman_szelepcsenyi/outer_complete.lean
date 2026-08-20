import RequestProject.Machine

/-!
# The inductive counting construction

Given a nondeterministic branching program we build, by Immerman and Szelepcsényi's
inductive counting method, a nondeterministic branching program of polynomially larger
size accepting exactly the complementary language.
-/

namespace CS

namespace Compl

variable {n : ℕ} (P : Setup n)

/-! ### The invariant -/

variable (x : Fin n → Bool)

/-- The set of configurations of the original machine reachable in at most `i` steps. -/

lemma outer_complete (hno : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y) (d : ℕ) :
    ∀ (p : ℕ) (s : CSt P.N P.V), p + d = P.N → s.pc = 1 → (s.v : ℕ) = p → (s.i : ℕ) < P.N →
      (s.r : ℕ) = (RS P x (s.i : ℕ)).ncard → (s.r2 : ℕ) = Cnt P x ((s.i : ℕ) + 1) p →
      ∃ t : CSt P.N P.V, Relation.ReflTransGen (cstep P x) s t ∧ t.pc = 1 ∧ t.i = s.i ∧
        t.r = s.r ∧ (t.v : ℕ) = P.N ∧ (t.r2 : ℕ) = Cnt P x ((s.i : ℕ) + 1) P.N := by
  classical
  induction d with
  | zero =>
      intro p s hpd hpc hv hi hr hr2
      have hp : p = P.N := by omega
      subst hp
      exact ⟨s, .refl, hpc, rfl, rfl, hv, hr2⟩
  | succ d ih =>
      intro p s hpd hpc hv hi hr hr2
      have hpN : p < P.N := by omega
      have hstep1 : cstep P x s { s with pc := 2, c := 0, u := 0, fnd := false } :=
        Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨hpc, by omega, rfl⟩))))
      obtain ⟨t1, ht1, ht1pc, ht1i, ht1r, ht1r2, ht1v, ht1u, ht1c, ht1f⟩ :=
        inner_complete P x hno P.N 0 { s with pc := 2, c := 0, u := 0, fnd := false }
          (by omega) rfl (by simp) (by simp [Cnt_zero]) (by simp)
      have ht1i' : t1.i = s.i := ht1i
      have ht1r' : t1.r = s.r := ht1r
      have ht1r2' : t1.r2 = s.r2 := ht1r2
      have ht1v' : t1.v = s.v := ht1v
      have ht1c' : (t1.c : ℕ) = Cnt P x (s.i : ℕ) P.N := ht1c
      have ht1f' : t1.fnd = true ↔ ∃ y ∈ RS P x (s.i : ℕ), P.idx y < P.N ∧
          (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ))) := ht1f
      have hmemiff : t1.fnd = true ↔ P.vAt p ∈ RS P x ((s.i : ℕ) + 1) := by
        rw [ht1f', hv]
        constructor
        · rintro ⟨y, hy, -, (rfl | hstep)⟩
          · exact Or.inl hy
          · exact Or.inr ⟨y, hy, hstep⟩
        · rintro (hm | ⟨y, hy, hstep⟩)
          · exact ⟨_, hm, P.idx_lt _, Or.inl rfl⟩
          · exact ⟨y, hy, P.idx_lt _, Or.inr hstep⟩
      have hcr : t1.c = t1.r := by
        apply Fin.ext
        rw [ht1c', ht1r', hr, Cnt_full]
      have hr2le : (s.r2 : ℕ) ≤ p := by
        rw [hr2]; exact Cnt_le P x _ _ (by omega)
      obtain ⟨r2', hr2'⟩ : ∃ r2' : Fin (P.N + 1),
          (r2' : ℕ) = (t1.r2 : ℕ) + (if t1.fnd = true then 1 else 0) := by
        refine ⟨⟨(t1.r2 : ℕ) + (if t1.fnd = true then 1 else 0), ?_⟩, rfl⟩
        rw [ht1r2']
        split_ifs <;> omega
      obtain ⟨v', hv'⟩ : ∃ v' : Fin (P.N + 1), (v' : ℕ) = (t1.v : ℕ) + 1 := by
        refine ⟨⟨(t1.v : ℕ) + 1, ?_⟩, rfl⟩
        rw [ht1v']
        omega
      have hstep2 : cstep P x t1 { t1 with pc := 1, r2 := r2', v := v' } :=
        Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨ht1pc, ht1u, hcr, r2', v', hr2', hv', rfl⟩)))))
      have hnewr2 : (r2' : ℕ) = Cnt P x ((s.i : ℕ) + 1) ((v' : ℕ)) := by
        rw [hv', ht1v', hv, hr2', ht1r2', hr2]
        cases hb : t1.fnd
        · have hnm : P.vAt p ∉ RS P x ((s.i : ℕ) + 1) := by
            intro hm
            rw [hmemiff.mpr hm] at hb
            exact absurd hb (by decide)
          rw [Cnt_succ_not_mem P x _ _ hnm]
          simp
        · rw [Cnt_succ_mem P x _ _ hpN (hmemiff.mp hb)]
          simp
      obtain ⟨t, ht, htpc, hti, htr, htv, htr2⟩ :=
        ih (p + 1) { t1 with pc := 1, r2 := r2', v := v' } (by omega) rfl
          (by show (v' : ℕ) = p + 1; rw [hv', ht1v', hv])
          (by show ((t1.i : ℕ)) < P.N; rw [ht1i']; exact hi)
          (by show (t1.r : ℕ) = (RS P x ((t1.i : ℕ))).ncard; rw [ht1r', ht1i']; exact hr)
          (by
            show (r2' : ℕ) = Cnt P x ((t1.i : ℕ) + 1) (p + 1)
            have hvp : ((v' : ℕ)) = p + 1 := by rw [hv', ht1v', hv]
            rw [ht1i', ← hvp]
            exact hnewr2)
      refine ⟨t, (Relation.ReflTransGen.head hstep1 ht1).trans (Relation.ReflTransGen.head
        hstep2 ht), htpc, ?_, ?_, htv, ?_⟩
      · rw [hti]; exact ht1i'
      · rw [htr]; exact ht1r'
      · rw [htr2, ht1i']


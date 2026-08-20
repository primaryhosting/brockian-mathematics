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

lemma inner_complete (hno : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y) (d : ℕ) :
    ∀ (p : ℕ) (s : CSt P.N P.V), p + d = P.N → s.pc = 2 → (s.u : ℕ) = p →
      (s.c : ℕ) = Cnt P x (s.i : ℕ) p →
      (s.fnd = true ↔ ∃ y ∈ RS P x (s.i : ℕ), P.idx y < p ∧
        (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ)))) →
      ∃ t : CSt P.N P.V, Relation.ReflTransGen (cstep P x) s t ∧ t.pc = 2 ∧ t.i = s.i ∧
        t.r = s.r ∧ t.r2 = s.r2 ∧ t.v = s.v ∧ (t.u : ℕ) = P.N ∧
        (t.c : ℕ) = Cnt P x (s.i : ℕ) P.N ∧
        (t.fnd = true ↔ ∃ y ∈ RS P x (s.i : ℕ), P.idx y < P.N ∧
          (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ)))) := by
  classical
  induction d with
  | zero =>
      intro p s hpd hpc hu hc hfnd
      have hp : p = P.N := by omega
      subst hp
      exact ⟨s, .refl, hpc, rfl, rfl, rfl, rfl, hu, hc, hfnd⟩
  | succ d ih =>
      intro p s hpd hpc hu hc hfnd
      have hpN : p < P.N := by omega
      have hcp : (s.c : ℕ) ≤ p := by
        rw [hc]; exact Cnt_le P x _ _ (by omega)
      by_cases hmem : P.vAt p ∈ RS P x (s.i : ℕ)
      · -- count the vertex `vAt p`
        obtain ⟨c', hc'⟩ : ∃ c' : Fin (P.N + 1), (c' : ℕ) = (s.c : ℕ) + 1 :=
          ⟨⟨(s.c : ℕ) + 1, by omega⟩, rfl⟩
        obtain ⟨u', hu'⟩ : ∃ u' : Fin (P.N + 1), (u' : ℕ) = p + 1 := ⟨⟨p + 1, by omega⟩, rfl⟩
        set s1 : CSt P.N P.V := { s with pc := 3, w := P.st, j := 0 } with hs1
        have hstep1 : cstep P x s s1 :=
          Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
             ⟨hpc, by omega, rfl⟩)))))))
        obtain ⟨j', hj'le, hpath⟩ :=
          path_complete P x (s.i : ℕ) (P.vAt p) hmem s1 rfl rfl (by simp [hs1]) le_rfl
        set s2 : CSt P.N P.V := { s1 with j := j', w := P.vAt p } with hs2
        set f' : Bool := (s.fnd || decide (P.vAt p = P.vAt (s.v : ℕ)) ||
          decide (P.step x (P.vAt p) (P.vAt (s.v : ℕ)))) with hf'def
        set s3 : CSt P.N P.V := { s2 with pc := 2, c := c', u := u', fnd := f' } with hs3
        have hfndnew : f' = true ↔ ∃ y ∈ RS P x (s.i : ℕ), P.idx y < p + 1 ∧
            (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ))) := by
          rw [hf'def]
          simp only [Bool.or_eq_true, decide_eq_true_eq]
          constructor
          · rintro ((h1 | h1) | h1)
            · obtain ⟨y, hy, hlt, hy2⟩ := hfnd.mp h1
              exact ⟨y, hy, by omega, hy2⟩
            · exact ⟨P.vAt p, hmem, by rw [P.idx_vAt hpN]; omega, Or.inl h1⟩
            · exact ⟨P.vAt p, hmem, by rw [P.idx_vAt hpN]; omega, Or.inr h1⟩
          · rintro ⟨y, hy, hlt, hy2⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h1 | h1
            · exact Or.inl (Or.inl (hfnd.mpr ⟨y, hy, h1, hy2⟩))
            · have hyv : y = P.vAt p := by rw [← h1, P.vAt_idx]
              subst hyv
              rcases hy2 with h2 | h2
              · exact Or.inl (Or.inr h2)
              · exact Or.inr h2
        have hB : Base9 P s2 s3 := by
          refine ⟨rfl, ?_, ?_, ?_, ?_, c', u', f', ?_, ?_, rfl⟩
          · show P.vAt p = P.vAt (s.u : ℕ)
            rw [hu]
          · show ¬ P.acc (P.vAt p)
            exact not_acc_of_mem_RS P x hno _ _ hmem
          · show (s.u : ℕ) < P.N
            omega
          · show (s.c : ℕ) < P.N
            omega
          · show (c' : ℕ) = (s.c : ℕ) + 1
            exact hc'
          · show (u' : ℕ) = (s.u : ℕ) + 1
            omega
        have hqa : qa P s2 s3 = P.vAt p := by
          rw [qa, if_neg (by rintro ⟨-, h3⟩; exact absurd (show (2 : Fin 5) = 3 from h3) (by decide))]
          show P.vAt (s.u : ℕ) = P.vAt p
          rw [hu]
        have hqb : qb P s2 s3 = P.vAt (s.v : ℕ) := by
          rw [qb, if_neg (by rintro ⟨-, h3⟩; exact absurd (show (2 : Fin 5) = 3 from h3) (by decide))]
        have hstep3 : cstep P x s2 s3 := by
          by_cases hP0 : (s2.fnd = true ∨ P.vAt (s2.u : ℕ) = P.vAt (s2.v : ℕ))
          · refine Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              ⟨hB, hP0, ?_⟩)))))))
            show f' = true
            rw [hf'def]
            rcases hP0 with h1 | h1
            · simp [show s.fnd = true from h1]
            · have h2 : P.vAt p = P.vAt (s.v : ℕ) := by
                rw [← h1]; show P.vAt p = P.vAt (s.u : ℕ); rw [hu]
              simp [h2]
          · by_cases hg : (P.edg (P.vAt p) (P.vAt (s.v : ℕ))).eval x = true
            · refine Or.inr (Or.inl ⟨Or.inr ⟨hB, hP0, ?_⟩, ?_⟩)
              · show f' = true
                rw [hf'def]
                simp [show P.step x (P.vAt p) (P.vAt (s.v : ℕ)) from hg]
              · rw [hqa, hqb]; exact hg
            · refine Or.inr (Or.inr ⟨⟨hB, hP0, ?_⟩, ?_⟩)
              · show f' = false
                push_neg at hP0
                rw [hf'def]
                have h1 : s.fnd = false := by
                  cases hb : s.fnd
                  · rfl
                  · exact absurd (show s2.fnd = true from hb) hP0.1
                have h2 : ¬ (P.vAt p = P.vAt (s.v : ℕ)) := by
                  intro h
                  refine hP0.2 ?_
                  show P.vAt (s.u : ℕ) = P.vAt (s.v : ℕ)
                  rw [hu]; exact h
                have h3 : ¬ P.step x (P.vAt p) (P.vAt (s.v : ℕ)) := hg
                simp [h1, h2, h3]
              · rw [hqa, hqb]
                simpa using hg
        obtain ⟨t, ht, ht2⟩ := ih (p + 1) s3 (by omega) rfl (by exact hu')
          (by
            show (c' : ℕ) = Cnt P x (s.i : ℕ) (p + 1)
            rw [hc', hc, Cnt_succ_mem P x _ _ hpN hmem])
          (by exact hfndnew)
        refine ⟨t, ?_, ht2.1, ht2.2.1, ht2.2.2.1, ht2.2.2.2.1, ht2.2.2.2.2.1,
          ht2.2.2.2.2.2.1, ht2.2.2.2.2.2.2.1, ht2.2.2.2.2.2.2.2⟩
        exact (Relation.ReflTransGen.head hstep1 (hpath.tail hstep3)).trans ht
      · -- skip the vertex `vAt p`
        obtain ⟨u', hu'⟩ : ∃ u' : Fin (P.N + 1), (u' : ℕ) = p + 1 := ⟨⟨p + 1, by omega⟩, rfl⟩
        have hstep1 : cstep P x s { s with u := u' } :=
          Or.inl (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            ⟨hpc, by omega, u', by omega, rfl⟩))))))
        have hfnd1 : ({ s with u := u' } : CSt P.N P.V).fnd = true ↔
            ∃ y ∈ RS P x (s.i : ℕ), P.idx y < p + 1 ∧
              (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ))) := by
          show s.fnd = true ↔ _
          rw [hfnd]
          constructor
          · rintro ⟨y, hy, hlt, hy2⟩
            exact ⟨y, hy, by omega, hy2⟩
          · rintro ⟨y, hy, hlt, hy2⟩
            refine ⟨y, hy, ?_, hy2⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h1 | h1
            · exact h1
            · exact absurd (by rw [← h1, P.vAt_idx]; exact hy) hmem
        obtain ⟨t, ht, ht2⟩ := ih (p + 1) { s with u := u' } (by omega) hpc (by exact hu')
          (by
            show (s.c : ℕ) = Cnt P x (s.i : ℕ) (p + 1)
            rw [hc, Cnt_succ_not_mem P x _ _ hmem])
          hfnd1
        refine ⟨t, ?_, ht2.1, ht2.2.1, ht2.2.2.1, ht2.2.2.2.1, ht2.2.2.2.2.1,
          ht2.2.2.2.2.2.1, ht2.2.2.2.2.2.2.1, ht2.2.2.2.2.2.2.2⟩
        exact Relation.ReflTransGen.head hstep1 ht


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

lemma round_complete (hno : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y) (d : ℕ) :
    ∀ (m : ℕ) (s : CSt P.N P.V), m + d = P.N → s.pc = 0 → (s.i : ℕ) = m →
      (s.r : ℕ) = (RS P x m).ncard →
      ∃ t : CSt P.N P.V, Relation.ReflTransGen (cstep P x) s t ∧ t.pc = 0 ∧ (t.i : ℕ) = P.N := by
  induction d with
  | zero =>
      intro m s hmd hpc hi hr
      exact ⟨s, .refl, hpc, by omega⟩
  | succ d ih =>
      intro m s hmd hpc hi hr
      have hmN : m < P.N := by omega
      have hstep1 : cstep P x s { s with pc := 1, r2 := 0, v := 0 } :=
        Or.inl (Or.inr (Or.inl ⟨hpc, by omega, rfl⟩))
      obtain ⟨t1, ht1, ht1pc, ht1i, ht1r, ht1v, ht1r2⟩ :=
        outer_complete P x hno P.N 0 { s with pc := 1, r2 := 0, v := 0 } (by omega) rfl
          (by simp) (by show (s.i : ℕ) < P.N; omega)
          (by show (s.r : ℕ) = (RS P x (s.i : ℕ)).ncard; rw [hi]; exact hr)
          (by simp [Cnt_zero])
      have ht1i' : t1.i = s.i := ht1i
      have ht1r2' : (t1.r2 : ℕ) = Cnt P x ((s.i : ℕ) + 1) P.N := ht1r2
      obtain ⟨i', hi'⟩ : ∃ i' : Fin (P.N + 1), (i' : ℕ) = (t1.i : ℕ) + 1 := by
        refine ⟨⟨(t1.i : ℕ) + 1, ?_⟩, rfl⟩
        rw [ht1i', hi]
        omega
      have hstep2 : cstep P x t1 { t1 with pc := 0, i := i', r := t1.r2 } :=
        Or.inl (Or.inr (Or.inr (Or.inl ⟨ht1pc, ht1v, i', hi', rfl⟩)))
      obtain ⟨t, ht, htpc, hti⟩ :=
        ih (m + 1) { t1 with pc := 0, i := i', r := t1.r2 } (by omega) rfl
          (by show (i' : ℕ) = m + 1; rw [hi', ht1i', hi])
          (by
            show (t1.r2 : ℕ) = (RS P x (m + 1)).ncard
            rw [ht1r2', hi, Cnt_full])
      exact ⟨t, (Relation.ReflTransGen.head hstep1 ht1).trans
        (Relation.ReflTransGen.head hstep2 ht), htpc, hti⟩

/-- If no accepting configuration of the original machine is reachable, then the
complementing machine has an accepting run. -/

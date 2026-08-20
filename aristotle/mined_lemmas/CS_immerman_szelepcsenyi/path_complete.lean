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

lemma path_complete (m : ℕ) : ∀ (y : P.V), y ∈ RS P x m → ∀ (s : CSt P.N P.V), s.pc = 3 →
    s.w = P.st → (s.j : ℕ) = 0 → m ≤ (s.i : ℕ) →
    ∃ j' : Fin (P.N + 1), (j' : ℕ) ≤ m ∧
      Relation.ReflTransGen (cstep P x) s { s with j := j', w := y } := by
  induction m with
  | zero =>
      intro y hy s hpc hw hj hm
      have hyst : y = P.st := hy
      refine ⟨s.j, by omega, ?_⟩
      have hst : ({ s with j := s.j, w := y } : CSt P.N P.V) = s := by
        rw [hyst, ← hw]
      rw [hst]
  | succ m ih =>
      intro y hy s hpc hw hj hm
      have hiN : (s.i : ℕ) ≤ P.N := by have := s.i.isLt; omega
      rcases hy with hy | ⟨y', hy', hstep⟩
      · obtain ⟨j', hj', hpath⟩ := ih y hy s hpc hw hj (by omega)
        exact ⟨j', by omega, hpath⟩
      · obtain ⟨j', hj'le, hpath⟩ := ih y' hy' s hpc hw hj (by omega)
        refine ⟨⟨(j' : ℕ) + 1, by omega⟩, by simp; omega, ?_⟩
        refine hpath.tail ?_
        have hpc2 : ({ s with j := j', w := y' } : CSt P.N P.V).pc = 3 := hpc
        have hpc3 : ({ s with j := (⟨(j' : ℕ) + 1, by omega⟩ : Fin (P.N + 1)), w := y } :
            CSt P.N P.V).pc = 3 := hpc
        refine Or.inr (Or.inl ⟨Or.inl ⟨hpc2, ?_, ⟨(j' : ℕ) + 1, by omega⟩, y, rfl, rfl⟩, ?_⟩)
        · show (j' : ℕ) < (s.i : ℕ)
          omega
        · rw [qa, if_pos ⟨hpc2, hpc3⟩, qb, if_pos ⟨hpc2, hpc3⟩]
          exact hstep


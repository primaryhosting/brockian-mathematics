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

lemma complete (hno : ∀ y, Relation.ReflTransGen (P.step x) P.st y → ¬ P.acc y) :
    ∃ t : CSt P.N P.V, t.pc = 4 ∧ Relation.ReflTransGen (cstep P x) (cstart P) t := by
  obtain ⟨t, ht, htpc, hti⟩ :=
    round_complete P x hno P.N 0 (cstart P) (by omega) rfl (by simp [cstart])
      (by
        show ((cstart P).r : ℕ) = (RS P x 0).ncard
        simp [cstart, RS])
  refine ⟨{ t with pc := 4 }, rfl, ht.tail ?_⟩
  exact Or.inl (Or.inl ⟨htpc, hti, rfl⟩)

/-! ### The complementing branching program -/

/-- The complementing nondeterministic branching program. -/

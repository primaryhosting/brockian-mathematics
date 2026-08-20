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

lemma reach_cases (n : ℕ) (x : Fin n → Bool) (w : Unit ⊕ Fin n ⊕ Unit)
    (hw : Relation.ReflTransGen ((machine n).step x) (Sum.inl ()) w) :
    w = Sum.inl () ∨ (∃ i, w = Sum.inr (Sum.inl i)) ∨ (∃ i, x i = true) := by
  induction hw with
  | refl => exact Or.inl rfl
  | tail _ hbc ih =>
      rcases ih with rfl | ⟨i, rfl⟩ | h
      · rename_i c _
        rcases c with ⟨⟩ | ⟨i | ⟨⟩⟩
        · exact absurd hbc (by simp [machine, NBP.step, Guard.eval])
        · exact Or.inr (Or.inl ⟨i, rfl⟩)
        · exact absurd hbc (by simp [machine, NBP.step, Guard.eval])
      · rename_i c _
        rcases c with ⟨⟩ | ⟨i' | ⟨⟩⟩
        · exact absurd hbc (by simp [machine, NBP.step, Guard.eval])
        · exact absurd hbc (by simp [machine, NBP.step, Guard.eval])
        · refine Or.inr (Or.inr ⟨i, ?_⟩)
          have : (Guard.bit i true).eval x = true := hbc
          simpa [Guard.eval] using this
      · exact Or.inr (Or.inr h)


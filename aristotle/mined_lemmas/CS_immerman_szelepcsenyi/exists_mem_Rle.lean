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

lemma exists_mem_Rle {y : V} (h : Relation.ReflTransGen E st y) :
    ∃ i, y ∈ Rle E st i := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hbc ih =>
      obtain ⟨i, hi⟩ := ih
      exact ⟨i + 1, Or.inr ⟨_, hi, hbc⟩⟩


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

lemma Rle_subset_reach {i : ℕ} {y : V} (h : y ∈ Rle E st i) :
    Relation.ReflTransGen E st y := by
  induction i generalizing y with
  | zero => cases h; exact Relation.ReflTransGen.refl
  | succ i ih =>
      rcases h with h | ⟨z, hz, hzy⟩
      · exact ih h
      · exact (ih hz).tail hzy


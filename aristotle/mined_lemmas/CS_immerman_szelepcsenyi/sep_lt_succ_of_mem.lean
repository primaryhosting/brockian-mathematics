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

lemma sep_lt_succ_of_mem {i p : ℕ} (hp : p < P.N) (h : P.vAt p ∈ RS P x i) :
    {y ∈ RS P x i | P.idx y < p + 1} = insert (P.vAt p) {y ∈ RS P x i | P.idx y < p} := by
  ext y
  simp only [Set.mem_sep_iff, Set.mem_insert_iff]
  constructor
  · rintro ⟨hy, hlt⟩
    rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h1 | h1
    · exact Or.inr ⟨hy, h1⟩
    · exact Or.inl (by rw [← h1, P.vAt_idx])
  · rintro (rfl | ⟨hy, hlt⟩)
    · exact ⟨h, by simp [P.idx_vAt hp]⟩
    · exact ⟨hy, by omega⟩


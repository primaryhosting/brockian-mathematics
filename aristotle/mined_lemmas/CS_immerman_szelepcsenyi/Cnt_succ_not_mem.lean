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

lemma Cnt_succ_not_mem (i p : ℕ) (h : P.vAt p ∉ RS P x i) :
    Cnt P x i (p + 1) = Cnt P x i p := by
  have hsplit : {y ∈ RS P x i | P.idx y < p + 1} = {y ∈ RS P x i | P.idx y < p} := by
    ext y
    simp only [Set.mem_sep_iff]
    constructor
    · rintro ⟨hy, hlt⟩
      refine ⟨hy, ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hlt with h1 | h1
      · exact h1
      · exact absurd (by rw [← h1, P.vAt_idx]; exact hy) h
    · rintro ⟨hy, hlt⟩; exact ⟨hy, by omega⟩
  rw [Cnt, hsplit]; rfl


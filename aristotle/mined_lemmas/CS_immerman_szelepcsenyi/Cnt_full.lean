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

lemma Cnt_full (i : ℕ) : Cnt P x i P.N = (RS P x i).ncard := by
  have hs : {y ∈ RS P x i | P.idx y < P.N} = RS P x i := by
    ext y; simp [P.idx_lt y]
  rw [Cnt, hs]


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

lemma vAt_not_mem_sep {i p : ℕ} (hp : p < P.N) :
    P.vAt p ∉ {y ∈ RS P x i | P.idx y < p} := by
  rintro ⟨-, hlt⟩
  rw [P.idx_vAt hp] at hlt
  omega


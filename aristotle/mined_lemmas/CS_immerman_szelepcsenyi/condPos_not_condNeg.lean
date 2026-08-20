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

lemma condPos_not_condNeg {s t : CSt P.N P.V} (h : CondPos P s t) : ¬ CondNeg P s t := by
  rintro ⟨hB, -, hf⟩
  rcases h with hE | ⟨-, -, hf'⟩
  · have h2 := Base9_tpc P hB
    rw [Ext_tpc P hE] at h2; exact absurd h2 (by decide)
  · rw [hf] at hf'; exact absurd hf' (by decide)


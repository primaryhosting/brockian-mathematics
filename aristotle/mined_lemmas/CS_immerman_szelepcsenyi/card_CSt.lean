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

lemma card_CSt (N : ℕ) (V : Type) [Fintype V] :
    Fintype.card (CSt N V) = 10 * (N + 1) ^ 7 * Fintype.card V := by
  rw [Fintype.card_congr (CSt.equivProd N V)]
  simp [Fintype.card_prod]
  ring

/-! ### The transitions of the complementing program -/

variable (P : Setup n)

/-- The transitions of the inner loop that finish a guessed path, apart from the update
of the `fnd` flag (which involves an edge query). -/

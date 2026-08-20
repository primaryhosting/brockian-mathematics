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

lemma cNBP_size (P : Setup n) : (cNBP P).size = 10 * (P.N + 1) ^ 7 * P.N := by
  show Fintype.card (CSt P.N P.V) = _
  rw [card_CSt, P.card_V]


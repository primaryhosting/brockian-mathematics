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

def InNL (L : Language) : Prop :=
  ∃ c k : ℕ, ∀ n : ℕ, ∃ B : NBP n, B.size ≤ c * (n + 1) ^ k ∧ ∀ x, (B.Accepts x ↔ L n x)

/-- Nondeterministic logarithmic space. -/

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

def InvRound (s : CSt P.N P.V) : Prop :=
  (s.i : ℕ) ≤ P.N ∧ (s.r : ℕ) = (RS P x (s.i : ℕ)).ncard ∧ Cert P x (s.i : ℕ)

/-- The invariant at the top of the outer loop. -/

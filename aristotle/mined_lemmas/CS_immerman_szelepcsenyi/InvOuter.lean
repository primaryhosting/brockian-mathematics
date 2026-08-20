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

def InvOuter (s : CSt P.N P.V) : Prop :=
  (s.i : ℕ) < P.N ∧ (s.r : ℕ) = (RS P x (s.i : ℕ)).ncard ∧ Cert P x (s.i : ℕ) ∧
    (s.v : ℕ) ≤ P.N ∧ (s.r2 : ℕ) = Cnt P x ((s.i : ℕ) + 1) (s.v : ℕ) ∧
    (0 < (s.v : ℕ) → Cert P x ((s.i : ℕ) + 1))

/-- The invariant during one pass of the outer loop. -/

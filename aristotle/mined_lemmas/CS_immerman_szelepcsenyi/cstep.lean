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

def cstep (x : Fin n → Bool) (s t : CSt P.N P.V) : Prop :=
  Uncond P s t
    ∨ (CondPos P s t ∧ (P.edg (qa P s t) (qb P s t)).eval x = true)
    ∨ (CondNeg P s t ∧ (P.edg (qa P s t) (qb P s t)).eval x = false)

/-- The start state of the complementing program. -/

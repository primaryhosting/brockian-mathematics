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

def qb (s t : CSt P.N P.V) : P.V := if s.pc = 3 ∧ t.pc = 3 then t.w else P.vAt (s.v : ℕ)

open Classical in
/-- The guards of the complementing program. -/

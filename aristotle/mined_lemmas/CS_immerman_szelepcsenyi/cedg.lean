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

noncomputable def cedg (s t : CSt P.N P.V) : Guard n :=
  if Uncond P s t then Guard.always
  else if CondPos P s t then P.edg (qa P s t) (qb P s t)
  else if CondNeg P s t then (P.edg (qa P s t) (qb P s t)).neg
  else Guard.never

/-- The one-step relation of the complementing program on the input `x`. -/

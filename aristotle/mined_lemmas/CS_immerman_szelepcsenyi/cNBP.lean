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

noncomputable def cNBP (P : Setup n) : NBP n where
  V := CSt P.N P.V
  fin := inferInstance
  start := cstart P
  accept := fun s => s.pc = 4
  edges := cedg P


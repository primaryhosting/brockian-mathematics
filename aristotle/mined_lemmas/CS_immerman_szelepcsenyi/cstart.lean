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

def cstart : CSt P.N P.V :=
  { pc := 0, i := 0, r := ⟨1, by have := P.hN; omega⟩, r2 := 0, v := 0, c := 0, u := 0, j := 0,
    w := P.st, fnd := false }


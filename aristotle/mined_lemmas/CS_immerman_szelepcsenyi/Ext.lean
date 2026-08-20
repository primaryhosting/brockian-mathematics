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

def Ext (s t : CSt P.N P.V) : Prop :=
  s.pc = 3 ∧ (s.j : ℕ) < (s.i : ℕ) ∧
    ∃ (j' : Fin (P.N + 1)) (w' : P.V), (j' : ℕ) = (s.j : ℕ) + 1 ∧ t = { s with j := j', w := w' }

/-- The transitions that do not query the input. -/

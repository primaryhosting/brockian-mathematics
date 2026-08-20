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

def CondPos (s t : CSt P.N P.V) : Prop :=
  Ext P s t ∨
    (Base9 P s t ∧ ¬ (s.fnd = true ∨ P.vAt (s.u : ℕ) = P.vAt (s.v : ℕ)) ∧ t.fnd = true)

/-- The transitions taken when the queried edge is absent. -/

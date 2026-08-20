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

def Base9 (s t : CSt P.N P.V) : Prop :=
  s.pc = 3 ∧ s.w = P.vAt (s.u : ℕ) ∧ ¬ P.acc s.w ∧ (s.u : ℕ) < P.N ∧ (s.c : ℕ) < P.N ∧
    ∃ (c' u' : Fin (P.N + 1)) (f' : Bool),
      (c' : ℕ) = (s.c : ℕ) + 1 ∧ (u' : ℕ) = (s.u : ℕ) + 1 ∧
      t = { s with pc := 2, c := c', u := u', fnd := f' }

/-- The transitions extending a guessed path by one edge (apart from the edge query). -/

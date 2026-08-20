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

def SInv (s : CSt P.N P.V) : Prop :=
  ∃ S : Set P.V, S ⊆ {y ∈ RS P x (s.i : ℕ) | P.idx y < (s.u : ℕ)} ∧ S.ncard = (s.c : ℕ) ∧
    (∀ y ∈ S, ¬ P.acc y) ∧
    (s.fnd = true ↔ ∃ y ∈ S, (y = P.vAt (s.v : ℕ) ∨ P.step x y (P.vAt (s.v : ℕ))))

/-- The invariant at the top of the round loop. -/

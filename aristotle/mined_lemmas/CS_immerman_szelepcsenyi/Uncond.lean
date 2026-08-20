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

def Uncond (s t : CSt P.N P.V) : Prop :=
  (s.pc = 0 ∧ (s.i : ℕ) = P.N ∧ t = { s with pc := 4 })
  ∨ (s.pc = 0 ∧ (s.i : ℕ) < P.N ∧ t = { s with pc := 1, r2 := 0, v := 0 })
  ∨ (s.pc = 1 ∧ (s.v : ℕ) = P.N ∧ ∃ i' : Fin (P.N + 1), (i' : ℕ) = (s.i : ℕ) + 1 ∧
      t = { s with pc := 0, i := i', r := s.r2 })
  ∨ (s.pc = 1 ∧ (s.v : ℕ) < P.N ∧ t = { s with pc := 2, c := 0, u := 0, fnd := false })
  ∨ (s.pc = 2 ∧ (s.u : ℕ) = P.N ∧ s.c = s.r ∧ ∃ r2' v' : Fin (P.N + 1),
      (r2' : ℕ) = (s.r2 : ℕ) + (if s.fnd then 1 else 0) ∧ (v' : ℕ) = (s.v : ℕ) + 1 ∧
      t = { s with pc := 1, r2 := r2', v := v' })
  ∨ (s.pc = 2 ∧ (s.u : ℕ) < P.N ∧ ∃ u' : Fin (P.N + 1), (u' : ℕ) = (s.u : ℕ) + 1 ∧
      t = { s with u := u' })
  ∨ (s.pc = 2 ∧ (s.u : ℕ) < P.N ∧ t = { s with pc := 3, w := P.st, j := 0 })
  ∨ (Base9 P s t ∧ (s.fnd = true ∨ P.vAt (s.u : ℕ) = P.vAt (s.v : ℕ)) ∧ t.fnd = true)

/-- The transitions taken when the queried edge is present. -/

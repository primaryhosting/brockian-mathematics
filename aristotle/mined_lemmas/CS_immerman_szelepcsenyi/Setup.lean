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

lemma Setup.card_V (P : Setup n) : Fintype.card P.V = P.N := by
  simpa using Fintype.card_congr P.e

/-! ### The states of the complementing program -/

/-- A state of the complementing machine: a program counter together with a fixed number
of counters (each at most `N`), one configuration of the original machine and one
Boolean flag. -/
structure CSt (N : ℕ) (V : Type) where
  /-- Program counter: `0` round loop, `1` outer loop, `2` inner loop, `3` path guessing,
  `4` accept. -/
  pc : Fin 5
  /-- The current round (`= level of the reachability set`). -/
  i : Fin (N + 1)
  /-- The (verified) size of the current level. -/
  r : Fin (N + 1)
  /-- The accumulator for the size of the next level. -/
  r2 : Fin (N + 1)
  /-- The position of the outer loop. -/
  v : Fin (N + 1)
  /-- The number of vertices counted in the inner loop. -/
  c : Fin (N + 1)
  /-- The position of the inner loop. -/
  u : Fin (N + 1)
  /-- The length of the path guessed so far. -/
  j : Fin (N + 1)
  /-- The endpoint of the path guessed so far. -/
  w : V
  /-- Whether the outer loop vertex was already found to be in the next level. -/
  fnd : Bool

/-- The states of the complementing machine as a product type. -/

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

@[simp] lemma Guard.eval_neg {n : ℕ} (g : Guard n) (x : Fin n → Bool) :
    (g.neg).eval x = !(g.eval x) := by
  cases g with
  | never => rfl
  | always => rfl
  | bit i b => cases hb : x i <;> cases b <;> simp [Guard.eval, Guard.neg, hb]

/-- A nondeterministic branching program on inputs of length `n`. -/
structure NBP (n : ℕ) : Type 1 where
  /-- The set of configurations. -/
  V : Type
  /-- Finiteness of the configuration set. -/
  fin : Fintype V
  /-- The initial configuration. -/
  start : V
  /-- The accepting configurations. -/
  accept : V → Prop
  /-- The guard of the edge from one configuration to another. -/
  edges : V → V → Guard n

attribute [instance] NBP.fin

/-- The one-step relation of an NBP on a given input. -/

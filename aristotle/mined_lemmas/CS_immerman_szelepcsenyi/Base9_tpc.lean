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

lemma Base9_tpc {s t : CSt P.N P.V} (h : Base9 P s t) : t.pc = 2 := by
  obtain ⟨-, -, -, -, -, c', u', f', -, -, rfl⟩ := h
  rfl


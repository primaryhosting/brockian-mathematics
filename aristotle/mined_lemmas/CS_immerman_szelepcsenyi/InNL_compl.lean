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

theorem InNL_compl {L : Language} (h : InNL L) : InNL (fun n x => ¬ L n x) := by
  obtain ⟨c, k, h⟩ := h
  refine ⟨10 * (c + 1) ^ 8, k * 8, fun n => ?_⟩
  obtain ⟨B, hsize, hacc⟩ := h n
  obtain ⟨B', hs', ha'⟩ := B.exists_complement
  refine ⟨B', le_trans hs' (size_bound c k B.size n hsize), fun x => ?_⟩
  rw [ha' x, hacc x]

/-- **The Immerman-Szelepcsényi theorem**: nondeterministic space is closed under
complement, `NL = coNL`. -/

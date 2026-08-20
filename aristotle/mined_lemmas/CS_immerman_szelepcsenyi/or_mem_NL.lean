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

theorem or_mem_NL : (fun n (x : Fin n → Bool) => ∃ i, x i = true) ∈ NL := by
  refine ⟨2, 1, fun n => ⟨OrLang.machine n, ?_, OrLang.machine_accepts n⟩⟩
  rw [OrLang.machine_size]
  simp
  omega

end CS


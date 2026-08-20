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

lemma inv_mk4 (s : CSt P.N P.V) (hpc : s.pc = 4) (h : Cert P x P.N) : Inv P x s := by
  refine ⟨?_, ?_, ?_, ?_, fun _ => h⟩ <;>
    (intro hx; rw [hpc] at hx; exact absurd hx (by decide))

